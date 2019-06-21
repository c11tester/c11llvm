//===-- CDSPass.cpp - xxx -------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file is a modified version of ThreadSanitizer.cpp, a part of a race detector.
//
// The tool is under development, for the details about previous versions see
// http://code.google.com/p/data-race-test
//
// The instrumentation phase is quite simple:
//   - Insert calls to run-time library before every memory access.
//      - Optimizations may apply to avoid instrumenting some of the accesses.
//   - Insert calls at function entry/exit.
// The rest is handled by the run-time library.
//===----------------------------------------------------------------------===//

#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/CaptureTracking.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/ProfileData/InstrProf.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/AtomicOrdering.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <vector>

using namespace llvm;

#define DEBUG_TYPE "CDS"
#include <llvm/IR/DebugLoc.h>

Value *getPosition( Instruction * I, IRBuilder <> IRB, bool print = false)
{
	const DebugLoc & debug_location = I->getDebugLoc ();
	std::string position_string;
	{
		llvm::raw_string_ostream position_stream (position_string);
		debug_location . print (position_stream);
	}

	if (print) {
		errs() << position_string;
	}

	return IRB . CreateGlobalStringPtr (position_string);
}

STATISTIC(NumInstrumentedReads, "Number of instrumented reads");
STATISTIC(NumInstrumentedWrites, "Number of instrumented writes");
STATISTIC(NumAccessesWithBadSize, "Number of accesses with bad size");
// STATISTIC(NumInstrumentedVtableWrites, "Number of vtable ptr writes");
// STATISTIC(NumInstrumentedVtableReads, "Number of vtable ptr reads");

STATISTIC(NumOmittedReadsBeforeWrite,
          "Number of reads ignored due to following writes");
STATISTIC(NumOmittedReadsFromConstantGlobals,
          "Number of reads from constant globals");
STATISTIC(NumOmittedReadsFromVtable, "Number of vtable reads");
STATISTIC(NumOmittedNonCaptured, "Number of accesses ignored due to capturing");

Type * OrdTy;

Type * Int8PtrTy;
Type * Int16PtrTy;
Type * Int32PtrTy;
Type * Int64PtrTy;

Type * VoidTy;

static const size_t kNumberOfAccessSizes = 4;

int getAtomicOrderIndex(AtomicOrdering order){
	switch (order) {
		case AtomicOrdering::Monotonic: 
			return (int)AtomicOrderingCABI::relaxed;
		//  case AtomicOrdering::Consume:         // not specified yet
		//    return AtomicOrderingCABI::consume;
		case AtomicOrdering::Acquire: 
			return (int)AtomicOrderingCABI::acquire;
		case AtomicOrdering::Release: 
			return (int)AtomicOrderingCABI::release;
		case AtomicOrdering::AcquireRelease: 
			return (int)AtomicOrderingCABI::acq_rel;
		case AtomicOrdering::SequentiallyConsistent: 
			return (int)AtomicOrderingCABI::seq_cst;
		default:
			// unordered or Not Atomic
			return -1;
	}
}

namespace {
	struct CDSPass : public FunctionPass {
		static char ID;
		CDSPass() : FunctionPass(ID) {}
		bool runOnFunction(Function &F) override; 

	private:
		void initializeCallbacks(Module &M);
		bool instrumentLoadOrStore(Instruction *I, const DataLayout &DL);
		bool isAtomicCall(Instruction *I);
		bool instrumentAtomic(Instruction *I, const DataLayout &DL);
		bool instrumentAtomicCall(CallInst *CI, const DataLayout &DL);
		void chooseInstructionsToInstrument(SmallVectorImpl<Instruction *> &Local,
											SmallVectorImpl<Instruction *> &All,
											const DataLayout &DL);
		bool addrPointsToConstantData(Value *Addr);
		int getMemoryAccessFuncIndex(Value *Addr, const DataLayout &DL);

		// Callbacks to run-time library are computed in doInitialization.
		Constant * CDSFuncEntry;
		Constant * CDSFuncExit;

		Constant * CDSLoad[kNumberOfAccessSizes];
		Constant * CDSStore[kNumberOfAccessSizes];
		Constant * CDSAtomicInit[kNumberOfAccessSizes];
		Constant * CDSAtomicLoad[kNumberOfAccessSizes];
		Constant * CDSAtomicStore[kNumberOfAccessSizes];
		Constant * CDSAtomicRMW[AtomicRMWInst::LAST_BINOP + 1][kNumberOfAccessSizes];
		Constant * CDSAtomicCAS_V1[kNumberOfAccessSizes];
		Constant * CDSAtomicCAS_V2[kNumberOfAccessSizes];
		Constant * CDSAtomicThreadFence;
	};
}

static bool isVtableAccess(Instruction *I) {
	if (MDNode *Tag = I->getMetadata(LLVMContext::MD_tbaa))
		return Tag->isTBAAVtableAccess();
	return false;
}

void CDSPass::initializeCallbacks(Module &M) {
	LLVMContext &Ctx = M.getContext();

	Type * Int1Ty = Type::getInt1Ty(Ctx);
	OrdTy = Type::getInt32Ty(Ctx);

	Int8PtrTy  = Type::getInt8PtrTy(Ctx);
	Int16PtrTy = Type::getInt16PtrTy(Ctx);
	Int32PtrTy = Type::getInt32PtrTy(Ctx);
	Int64PtrTy = Type::getInt64PtrTy(Ctx);

	VoidTy = Type::getVoidTy(Ctx);

	// Get the function to call from our untime library.
	for (unsigned i = 0; i < kNumberOfAccessSizes; i++) {
		const unsigned ByteSize = 1U << i;
		const unsigned BitSize = ByteSize * 8;

		std::string ByteSizeStr = utostr(ByteSize);
		std::string BitSizeStr = utostr(BitSize);

		Type *Ty = Type::getIntNTy(Ctx, BitSize);
		Type *PtrTy = Ty->getPointerTo();

		// uint8_t cds_atomic_load8 (void * obj, int atomic_index)
		// void cds_atomic_store8 (void * obj, int atomic_index, uint8_t val)
		SmallString<32> LoadName("cds_load" + BitSizeStr);
		SmallString<32> StoreName("cds_store" + BitSizeStr);
		SmallString<32> AtomicInitName("cds_atomic_init" + BitSizeStr);
		SmallString<32> AtomicLoadName("cds_atomic_load" + BitSizeStr);
		SmallString<32> AtomicStoreName("cds_atomic_store" + BitSizeStr);

		CDSLoad[i]  = M.getOrInsertFunction(LoadName, VoidTy, PtrTy);
		CDSStore[i] = M.getOrInsertFunction(StoreName, VoidTy, PtrTy);
		CDSAtomicInit[i] = M.getOrInsertFunction(AtomicInitName, 
								VoidTy, PtrTy, Ty, Int8PtrTy);
		CDSAtomicLoad[i]  = M.getOrInsertFunction(AtomicLoadName, 
								Ty, PtrTy, OrdTy, Int8PtrTy);
		CDSAtomicStore[i] = M.getOrInsertFunction(AtomicStoreName, 
								VoidTy, PtrTy, Ty, OrdTy, Int8PtrTy);

		for (int op = AtomicRMWInst::FIRST_BINOP; 
			op <= AtomicRMWInst::LAST_BINOP; ++op) {
			CDSAtomicRMW[op][i] = nullptr;
			std::string NamePart;

			if (op == AtomicRMWInst::Xchg)
				NamePart = "_exchange";
			else if (op == AtomicRMWInst::Add) 
				NamePart = "_fetch_add";
			else if (op == AtomicRMWInst::Sub)
				NamePart = "_fetch_sub";
			else if (op == AtomicRMWInst::And)
				NamePart = "_fetch_and";
			else if (op == AtomicRMWInst::Or)
				NamePart = "_fetch_or";
			else if (op == AtomicRMWInst::Xor)
				NamePart = "_fetch_xor";
			else
				continue;

			SmallString<32> AtomicRMWName("cds_atomic" + NamePart + BitSizeStr);
			CDSAtomicRMW[op][i] = M.getOrInsertFunction(AtomicRMWName, 
										Ty, PtrTy, Ty, OrdTy, Int8PtrTy);
		}

		// only supportes strong version
		SmallString<32> AtomicCASName_V1("cds_atomic_compare_exchange" + BitSizeStr + "_v1");
		SmallString<32> AtomicCASName_V2("cds_atomic_compare_exchange" + BitSizeStr + "_v2");
		CDSAtomicCAS_V1[i] = M.getOrInsertFunction(AtomicCASName_V1, 
								Ty, PtrTy, Ty, Ty, OrdTy, OrdTy, Int8PtrTy);
		CDSAtomicCAS_V2[i] = M.getOrInsertFunction(AtomicCASName_V2, 
								Int1Ty, PtrTy, PtrTy, Ty, OrdTy, OrdTy, Int8PtrTy);
	}

	CDSAtomicThreadFence = M.getOrInsertFunction("cds_atomic_thread_fence", 
													VoidTy, OrdTy, Int8PtrTy);
}

static bool shouldInstrumentReadWriteFromAddress(const Module *M, Value *Addr) {
	// Peel off GEPs and BitCasts.
	Addr = Addr->stripInBoundsOffsets();

	if (GlobalVariable *GV = dyn_cast<GlobalVariable>(Addr)) {
		if (GV->hasSection()) {
			StringRef SectionName = GV->getSection();
			// Check if the global is in the PGO counters section.
			auto OF = Triple(M->getTargetTriple()).getObjectFormat();
			if (SectionName.endswith(
			      getInstrProfSectionName(IPSK_cnts, OF, /*AddSegmentInfo=*/false)))
				return false;
		}

		// Check if the global is private gcov data.
		if (GV->getName().startswith("__llvm_gcov") ||
		GV->getName().startswith("__llvm_gcda"))
		return false;
	}

	// Do not instrument acesses from different address spaces; we cannot deal
	// with them.
	if (Addr) {
		Type *PtrTy = cast<PointerType>(Addr->getType()->getScalarType());
		if (PtrTy->getPointerAddressSpace() != 0)
			return false;
	}

	return true;
}

bool CDSPass::addrPointsToConstantData(Value *Addr) {
	// If this is a GEP, just analyze its pointer operand.
	if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(Addr))
		Addr = GEP->getPointerOperand();

	if (GlobalVariable *GV = dyn_cast<GlobalVariable>(Addr)) {
		if (GV->isConstant()) {
			// Reads from constant globals can not race with any writes.
			NumOmittedReadsFromConstantGlobals++;
			return true;
		}
	} else if (LoadInst *L = dyn_cast<LoadInst>(Addr)) {
		if (isVtableAccess(L)) {
			// Reads from a vtable pointer can not race with any writes.
			NumOmittedReadsFromVtable++;
			return true;
		}
	}
	return false;
}

bool CDSPass::runOnFunction(Function &F) {
	if (F.getName() == "main") {
		F.setName("user_main");
		errs() << "main replaced by user_main\n";
	}

	if (true) {
		initializeCallbacks( *F.getParent() );

		SmallVector<Instruction*, 8> AllLoadsAndStores;
		SmallVector<Instruction*, 8> LocalLoadsAndStores;
		SmallVector<Instruction*, 8> AtomicAccesses;

		std::vector<Instruction *> worklist;

		bool Res = false;
		const DataLayout &DL = F.getParent()->getDataLayout();

		// errs() << "--- " << F.getName() << "---\n";

		for (auto &B : F) {
			for (auto &I : B) {
				if ( (&I)->isAtomic() || isAtomicCall(&I) ) {
					AtomicAccesses.push_back(&I);
				} else if (isa<LoadInst>(I) || isa<StoreInst>(I)) {
					LocalLoadsAndStores.push_back(&I);
				} else if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
					// not implemented yet
				}
			}

			chooseInstructionsToInstrument(LocalLoadsAndStores, AllLoadsAndStores, DL);
		}

		for (auto Inst : AllLoadsAndStores) {
			// Res |= instrumentLoadOrStore(Inst, DL);
			// errs() << "load and store are replaced\n";
		}

		for (auto Inst : AtomicAccesses) {
			Res |= instrumentAtomic(Inst, DL);
		}

		if (F.getName() == "user_main") {
			// F.dump();
		}
	}

	return false;
}

void CDSPass::chooseInstructionsToInstrument(
	SmallVectorImpl<Instruction *> &Local, SmallVectorImpl<Instruction *> &All,
	const DataLayout &DL) {
	SmallPtrSet<Value*, 8> WriteTargets;
	// Iterate from the end.
	for (Instruction *I : reverse(Local)) {
		if (StoreInst *Store = dyn_cast<StoreInst>(I)) {
			Value *Addr = Store->getPointerOperand();
			if (!shouldInstrumentReadWriteFromAddress(I->getModule(), Addr))
				continue;
			WriteTargets.insert(Addr);
		} else {
			LoadInst *Load = cast<LoadInst>(I);
			Value *Addr = Load->getPointerOperand();
			if (!shouldInstrumentReadWriteFromAddress(I->getModule(), Addr))
				continue;
			if (WriteTargets.count(Addr)) {
				// We will write to this temp, so no reason to analyze the read.
				NumOmittedReadsBeforeWrite++;
				continue;
			}
			if (addrPointsToConstantData(Addr)) {
				// Addr points to some constant data -- it can not race with any writes.
				continue;
			}
		}
		Value *Addr = isa<StoreInst>(*I)
			? cast<StoreInst>(I)->getPointerOperand()
			: cast<LoadInst>(I)->getPointerOperand();
		if (isa<AllocaInst>(GetUnderlyingObject(Addr, DL)) &&
				!PointerMayBeCaptured(Addr, true, true)) {
			// The variable is addressable but not captured, so it cannot be
			// referenced from a different thread and participate in a data race
			// (see llvm/Analysis/CaptureTracking.h for details).
			NumOmittedNonCaptured++;
			continue;
		}
		All.push_back(I);
	}
	Local.clear();
}


bool CDSPass::instrumentLoadOrStore(Instruction *I,
									const DataLayout &DL) {
	IRBuilder<> IRB(I);
	bool IsWrite = isa<StoreInst>(*I);
	Value *Addr = IsWrite
		? cast<StoreInst>(I)->getPointerOperand()
		: cast<LoadInst>(I)->getPointerOperand();

	// swifterror memory addresses are mem2reg promoted by instruction selection.
	// As such they cannot have regular uses like an instrumentation function and
	// it makes no sense to track them as memory.
	if (Addr->isSwiftError())
	return false;

	int Idx = getMemoryAccessFuncIndex(Addr, DL);

//  not supported by CDS yet
/*  if (IsWrite && isVtableAccess(I)) {
    LLVM_DEBUG(dbgs() << "  VPTR : " << *I << "\n");
    Value *StoredValue = cast<StoreInst>(I)->getValueOperand();
    // StoredValue may be a vector type if we are storing several vptrs at once.
    // In this case, just take the first element of the vector since this is
    // enough to find vptr races.
    if (isa<VectorType>(StoredValue->getType()))
      StoredValue = IRB.CreateExtractElement(
          StoredValue, ConstantInt::get(IRB.getInt32Ty(), 0));
    if (StoredValue->getType()->isIntegerTy())
      StoredValue = IRB.CreateIntToPtr(StoredValue, IRB.getInt8PtrTy());
    // Call TsanVptrUpdate.
    IRB.CreateCall(TsanVptrUpdate,
                   {IRB.CreatePointerCast(Addr, IRB.getInt8PtrTy()),
                    IRB.CreatePointerCast(StoredValue, IRB.getInt8PtrTy())});
    NumInstrumentedVtableWrites++;
    return true;
  }

  if (!IsWrite && isVtableAccess(I)) {
    IRB.CreateCall(TsanVptrLoad,
                   IRB.CreatePointerCast(Addr, IRB.getInt8PtrTy()));
    NumInstrumentedVtableReads++;
    return true;
  }
*/

	Value *OnAccessFunc = nullptr;
	OnAccessFunc = IsWrite ? CDSStore[Idx] : CDSLoad[Idx];

	Type *ArgType = IRB.CreatePointerCast(Addr, Addr->getType())->getType();

	if ( ArgType != Int8PtrTy && ArgType != Int16PtrTy && 
			ArgType != Int32PtrTy && ArgType != Int64PtrTy ) {
		//errs() << "A load or store of type ";
		//errs() << *ArgType;
		//errs() << " is passed in\n";
		return false;	// if other types of load or stores are passed in
	}
	IRB.CreateCall(OnAccessFunc, IRB.CreatePointerCast(Addr, Addr->getType()));
	if (IsWrite) NumInstrumentedWrites++;
	else         NumInstrumentedReads++;
	return true;
}

bool CDSPass::instrumentAtomic(Instruction * I, const DataLayout &DL) {
	IRBuilder<> IRB(I);
	// LLVMContext &Ctx = IRB.getContext();

	if (auto *CI = dyn_cast<CallInst>(I)) {
		return instrumentAtomicCall(CI, DL);
	}

	Value *position = getPosition(I, IRB);

	if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
		Value *Addr = LI->getPointerOperand();
		int Idx=getMemoryAccessFuncIndex(Addr, DL);
		int atomic_order_index = getAtomicOrderIndex(LI->getOrdering());
		Value *order = ConstantInt::get(OrdTy, atomic_order_index);
		Value *args[] = {Addr, order, position};
		Instruction* funcInst=CallInst::Create(CDSAtomicLoad[Idx], args);
		ReplaceInstWithInst(LI, funcInst);
	} else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
		Value *Addr = SI->getPointerOperand();
		int Idx=getMemoryAccessFuncIndex(Addr, DL);
		int atomic_order_index = getAtomicOrderIndex(SI->getOrdering());
		Value *val = SI->getValueOperand();
		Value *order = ConstantInt::get(OrdTy, atomic_order_index);
		Value *args[] = {Addr, val, order, position};
		Instruction* funcInst=CallInst::Create(CDSAtomicStore[Idx], args);
		ReplaceInstWithInst(SI, funcInst);
	} else if (AtomicRMWInst *RMWI = dyn_cast<AtomicRMWInst>(I)) {
		Value *Addr = RMWI->getPointerOperand();
		int Idx=getMemoryAccessFuncIndex(Addr, DL);
		int atomic_order_index = getAtomicOrderIndex(RMWI->getOrdering());
		Value *val = RMWI->getValOperand();
		Value *order = ConstantInt::get(OrdTy, atomic_order_index);
		Value *args[] = {Addr, val, order, position};
		Instruction* funcInst = CallInst::Create(CDSAtomicRMW[RMWI->getOperation()][Idx], args);
		ReplaceInstWithInst(RMWI, funcInst);
	} else if (AtomicCmpXchgInst *CASI = dyn_cast<AtomicCmpXchgInst>(I)) {
		IRBuilder<> IRB(CASI);

		Value *Addr = CASI->getPointerOperand();
		int Idx=getMemoryAccessFuncIndex(Addr, DL);

		const unsigned ByteSize = 1U << Idx;
		const unsigned BitSize = ByteSize * 8;
		Type *Ty = Type::getIntNTy(IRB.getContext(), BitSize);
		Type *PtrTy = Ty->getPointerTo();

		Value *CmpOperand = IRB.CreateBitOrPointerCast(CASI->getCompareOperand(), Ty);
		Value *NewOperand = IRB.CreateBitOrPointerCast(CASI->getNewValOperand(), Ty);

		int atomic_order_index_succ = getAtomicOrderIndex(CASI->getSuccessOrdering());
		int atomic_order_index_fail = getAtomicOrderIndex(CASI->getFailureOrdering());
		Value *order_succ = ConstantInt::get(OrdTy, atomic_order_index_succ);
		Value *order_fail = ConstantInt::get(OrdTy, atomic_order_index_fail);

		Value *Args[] = {IRB.CreatePointerCast(Addr, PtrTy),
						 CmpOperand, NewOperand,
						 order_succ, order_fail, position};

		CallInst *funcInst = IRB.CreateCall(CDSAtomicCAS_V1[Idx], Args);
		Value *Success = IRB.CreateICmpEQ(funcInst, CmpOperand);

		Value *OldVal = funcInst;
		Type *OrigOldValTy = CASI->getNewValOperand()->getType();
		if (Ty != OrigOldValTy) {
			// The value is a pointer, so we need to cast the return value.
			OldVal = IRB.CreateIntToPtr(funcInst, OrigOldValTy);
		}

		Value *Res =
		  IRB.CreateInsertValue(UndefValue::get(CASI->getType()), OldVal, 0);
		Res = IRB.CreateInsertValue(Res, Success, 1);

		I->replaceAllUsesWith(Res);
		I->eraseFromParent();
	} else if (FenceInst *FI = dyn_cast<FenceInst>(I)) {
		int atomic_order_index = getAtomicOrderIndex(FI->getOrdering());
		Value *order = ConstantInt::get(OrdTy, atomic_order_index);
		Value *Args[] = {order, position};

		CallInst *funcInst = CallInst::Create(CDSAtomicThreadFence, Args);
		ReplaceInstWithInst(FI, funcInst);
		// errs() << "Thread Fences replaced\n";
	}
	return true;
}

bool CDSPass::isAtomicCall(Instruction *I) {
	if ( auto *CI = dyn_cast<CallInst>(I) ) {
		Function *fun = CI->getCalledFunction();
		if (fun == NULL)
			return false;

		StringRef funName = fun->getName();
		// todo: come up with better rules for function name checking
		if ( funName.contains("atomic_") ) {
			return true;
		} else if (funName.contains("atomic") ) {
			return true;
		}
	}

	return false;
}

bool CDSPass::instrumentAtomicCall(CallInst *CI, const DataLayout &DL) {
	IRBuilder<> IRB(CI);
	Function *fun = CI->getCalledFunction();
	StringRef funName = fun->getName();
	std::vector<Value *> parameters;

	User::op_iterator begin = CI->arg_begin();
	User::op_iterator end = CI->arg_end();
	for (User::op_iterator it = begin; it != end; ++it) {
		Value *param = *it;
		parameters.push_back(param);
	}

	// obtain source line number of the CallInst
	Value *position = getPosition(CI, IRB);

	// the pointer to the address is always the first argument
	Value *OrigPtr = parameters[0];
	int Idx = getMemoryAccessFuncIndex(OrigPtr, DL);
	if (Idx < 0)
		return false;

	const unsigned ByteSize = 1U << Idx;
	const unsigned BitSize = ByteSize * 8;
	Type *Ty = Type::getIntNTy(IRB.getContext(), BitSize);
	Type *PtrTy = Ty->getPointerTo();

	// atomic_init; args = {obj, order}
	if (funName.contains("atomic_init")) {
		Value *ptr = IRB.CreatePointerCast(OrigPtr, PtrTy);
		Value *val = IRB.CreateBitOrPointerCast(parameters[1], Ty);
		Value *args[] = {ptr, val, position};

		Instruction* funcInst = CallInst::Create(CDSAtomicInit[Idx], args);
		ReplaceInstWithInst(CI, funcInst);

		return true;
	}

	// atomic_load; args = {obj, order}
	if (funName.contains("atomic_load")) {
		bool isExplicit = funName.contains("atomic_load_explicit");

		Value *ptr = IRB.CreatePointerCast(OrigPtr, PtrTy);
		Value *order;
		if (isExplicit)
			order = IRB.CreateBitOrPointerCast(parameters[1], OrdTy);
		else 
			order = ConstantInt::get(OrdTy, 
							(int) AtomicOrderingCABI::seq_cst);
		Value *args[] = {ptr, order, position};
		
		Instruction* funcInst = CallInst::Create(CDSAtomicLoad[Idx], args);
		ReplaceInstWithInst(CI, funcInst);

		return true;
	} else if (funName.contains("atomic") && 
					funName.contains("load")) {
		// does this version of call always have an atomic order as an argument?
		Value *ptr = IRB.CreatePointerCast(OrigPtr, PtrTy);
		Value *order = IRB.CreateBitOrPointerCast(parameters[1], OrdTy);
		Value *args[] = {ptr, order, position};

		//Instruction* funcInst=CallInst::Create(CDSAtomicLoad[Idx], args);
		CallInst *funcInst = IRB.CreateCall(CDSAtomicLoad[Idx], args);
		Value *RetVal = IRB.CreateIntToPtr(funcInst, CI->getType());

		CI->replaceAllUsesWith(RetVal);
		CI->eraseFromParent();

		return true;
	}

	// atomic_store; args = {obj, val, order}
	if (funName.contains("atomic_store")) {
		bool isExplicit = funName.contains("atomic_store_explicit");
		Value *OrigVal = parameters[1];

		Value *ptr = IRB.CreatePointerCast(OrigPtr, PtrTy);
		Value *val = IRB.CreatePointerCast(OrigVal, Ty);
		Value *order;
		if (isExplicit)
			order = IRB.CreateBitOrPointerCast(parameters[2], OrdTy);
		else 
			order = ConstantInt::get(OrdTy, 
							(int) AtomicOrderingCABI::seq_cst);
		Value *args[] = {ptr, val, order, position};
		
		Instruction* funcInst = CallInst::Create(CDSAtomicStore[Idx], args);
		ReplaceInstWithInst(CI, funcInst);

		return true;
	} else if (funName.contains("atomic") && 
					funName.contains("EEEE5store")) {
		// does this version of call always have an atomic order as an argument?
		Value *OrigVal = parameters[1];

		Value *ptr = IRB.CreatePointerCast(OrigPtr, PtrTy);
		Value *val = IRB.CreatePointerCast(OrigVal, Ty);
		Value *order = IRB.CreateBitOrPointerCast(parameters[1], OrdTy);
		Value *args[] = {ptr, val, order, position};

		Instruction* funcInst = CallInst::Create(CDSAtomicStore[Idx], args);
		ReplaceInstWithInst(CI, funcInst);

		return true;
	}

	// atomic_fetch_*; args = {obj, val, order}
	if (funName.contains("atomic_fetch_") || 
			funName.contains("atomic_exchange") ) {
		bool isExplicit = funName.contains("_explicit");
		Value *OrigVal = parameters[1];

		int op;
		if ( funName.contains("_fetch_add") )
			op = AtomicRMWInst::Add;
		else if ( funName.contains("_fetch_sub") )
			op = AtomicRMWInst::Sub;
		else if ( funName.contains("_fetch_and") )
			op = AtomicRMWInst::And;
		else if ( funName.contains("_fetch_or") )
			op = AtomicRMWInst::Or;
		else if ( funName.contains("_fetch_xor") )
			op = AtomicRMWInst::Xor;
		else if ( funName.contains("atomic_exchange") )
			op = AtomicRMWInst::Xchg;
		else {
			errs() << "Unknown atomic read modify write operation\n";
			return false;
		}

		Value *ptr = IRB.CreatePointerCast(OrigPtr, PtrTy);
		Value *val = IRB.CreatePointerCast(OrigVal, Ty);
		Value *order;
		if (isExplicit)
			order = IRB.CreateBitOrPointerCast(parameters[2], OrdTy);
		else 
			order = ConstantInt::get(OrdTy, 
							(int) AtomicOrderingCABI::seq_cst);
		Value *args[] = {ptr, val, order, position};
		
		Instruction* funcInst = CallInst::Create(CDSAtomicRMW[op][Idx], args);
		ReplaceInstWithInst(CI, funcInst);

		return true;
	} else if (funName.contains("fetch")) {
		errs() << "atomic exchange captured. Not implemented yet. ";
		errs() << "See source file :";
		getPosition(CI, IRB, true);
	} else if (funName.contains("exchange") &&
			!funName.contains("compare_exchange") ) {
		errs() << "atomic exchange captured. Not implemented yet. ";
		errs() << "See source file :";
		getPosition(CI, IRB, true);
	}

	/* atomic_compare_exchange_*; 
	   args = {obj, expected, new value, order1, order2}
	*/
	if ( funName.contains("atomic_compare_exchange_") ) {
		bool isExplicit = funName.contains("_explicit");

		Value *Addr = IRB.CreatePointerCast(OrigPtr, PtrTy);
		Value *CmpOperand = IRB.CreatePointerCast(parameters[1], PtrTy);
		Value *NewOperand = IRB.CreateBitOrPointerCast(parameters[2], Ty);

		Value *order_succ, *order_fail;
		if (isExplicit) {
			order_succ = IRB.CreateBitOrPointerCast(parameters[3], OrdTy);
			order_fail = IRB.CreateBitOrPointerCast(parameters[4], OrdTy);
		} else  {
			order_succ = ConstantInt::get(OrdTy, 
							(int) AtomicOrderingCABI::seq_cst);
			order_fail = ConstantInt::get(OrdTy, 
							(int) AtomicOrderingCABI::seq_cst);
		}

		Value *args[] = {Addr, CmpOperand, NewOperand, 
							order_succ, order_fail, position};
		
		Instruction* funcInst = CallInst::Create(CDSAtomicCAS_V2[Idx], args);
		ReplaceInstWithInst(CI, funcInst);

		return true;
	} else if ( funName.contains("compare_exchange_strong") || 
				funName.contains("compare_exchange_weak") ) {
		Value *Addr = IRB.CreatePointerCast(OrigPtr, PtrTy);
		Value *CmpOperand = IRB.CreatePointerCast(parameters[1], PtrTy);
		Value *NewOperand = IRB.CreateBitOrPointerCast(parameters[2], Ty);

		Value *order_succ, *order_fail;
		order_succ = IRB.CreateBitOrPointerCast(parameters[3], OrdTy);
		order_fail = IRB.CreateBitOrPointerCast(parameters[4], OrdTy);

		Value *args[] = {Addr, CmpOperand, NewOperand, 
							order_succ, order_fail, position};
		Instruction* funcInst = CallInst::Create(CDSAtomicCAS_V2[Idx], args);
		ReplaceInstWithInst(CI, funcInst);

		return true;
	}

	return false;
}

int CDSPass::getMemoryAccessFuncIndex(Value *Addr,
										const DataLayout &DL) {
	Type *OrigPtrTy = Addr->getType();
	Type *OrigTy = cast<PointerType>(OrigPtrTy)->getElementType();
	assert(OrigTy->isSized());
	uint32_t TypeSize = DL.getTypeStoreSizeInBits(OrigTy);
	if (TypeSize != 8  && TypeSize != 16 &&
		TypeSize != 32 && TypeSize != 64 && TypeSize != 128) {
		NumAccessesWithBadSize++;
		// Ignore all unusual sizes.
		return -1;
	}
	size_t Idx = countTrailingZeros(TypeSize / 8);
	assert(Idx < kNumberOfAccessSizes);
	return Idx;
}


char CDSPass::ID = 0;

// Automatically enable the pass.
static void registerCDSPass(const PassManagerBuilder &,
							legacy::PassManagerBase &PM) {
	PM.add(new CDSPass());
}
static RegisterStandardPasses 
	RegisterMyPass(PassManagerBuilder::EP_OptimizerLast,
registerCDSPass);
