//===-- CDSPass.cpp - xxx -------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
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
#include "llvm/IR/CFG.h"
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
#include <list>
#include <vector>
// #include "llvm/Support/MathExtras.h"

#define DEBUG_TYPE "CDS"
using namespace llvm;

#define FUNCARRAYSIZE 4

STATISTIC(NumInstrumentedReads, "Number of instrumented reads");
STATISTIC(NumInstrumentedWrites, "Number of instrumented writes");
// STATISTIC(NumInstrumentedVtableWrites, "Number of vtable ptr writes");
// STATISTIC(NumInstrumentedVtableReads, "Number of vtable ptr reads");

STATISTIC(NumOmittedReadsBeforeWrite,
          "Number of reads ignored due to following writes");
STATISTIC(NumOmittedReadsFromConstantGlobals,
          "Number of reads from constant globals");
STATISTIC(NumOmittedReadsFromVtable, "Number of vtable reads");
STATISTIC(NumOmittedNonCaptured, "Number of accesses ignored due to capturing");

Type * Int8Ty;
Type * Int16Ty;
Type * Int32Ty;
Type * Int64Ty;
Type * OrdTy;

Type * Int8PtrTy;
Type * Int16PtrTy;
Type * Int32PtrTy;
Type * Int64PtrTy;

Type * VoidTy;

Constant * CDSLoad[FUNCARRAYSIZE];
Constant * CDSStore[FUNCARRAYSIZE];
Constant * CDSAtomicLoad[FUNCARRAYSIZE];
Constant * CDSAtomicStore[FUNCARRAYSIZE];
Constant * CDSAtomicRMW[AtomicRMWInst::LAST_BINOP + 1][FUNCARRAYSIZE];
Constant * CDSAtomicCAS[FUNCARRAYSIZE];
Constant * CDSAtomicThreadFence;

bool start = false;

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

int getTypeSize(Type* type) {
  if (type==Int32PtrTy) {
    return sizeof(int)*8;
  } else if (type==Int8PtrTy) {
    return sizeof(char)*8;
  } else if (type==Int16PtrTy) {
    return sizeof(short)*8;
  } else if (type==Int64PtrTy) {
    return sizeof(long long int)*8;
  } else {
    return sizeof(void*)*8;
  }

  return -1;
}

static int sizetoindex(int size) {
  switch(size) {
    case 8:     return 0;
    case 16:    return 1;
    case 32:    return 2;
    case 64:    return 3;
  }
  return -1;
}

namespace {
  struct CDSPass : public FunctionPass {
    static char ID;
    CDSPass() : FunctionPass(ID) {}
    bool runOnFunction(Function &F) override; 

  private:
    void initializeCallbacks(Module &M);
    bool instrumentLoadOrStore(Instruction *I, const DataLayout &DL);
    bool instrumentAtomic(Instruction *I);
    void chooseInstructionsToInstrument(SmallVectorImpl<Instruction *> &Local,
                                      SmallVectorImpl<Instruction *> &All,
                                      const DataLayout &DL);
    bool addrPointsToConstantData(Value *Addr);
  };
}

void CDSPass::initializeCallbacks(Module &M) {
  LLVMContext &Ctx = M.getContext();

  Int8Ty  = Type::getInt8Ty(Ctx);
  Int16Ty = Type::getInt16Ty(Ctx);
  Int32Ty = Type::getInt32Ty(Ctx);
  Int64Ty = Type::getInt64Ty(Ctx);
  OrdTy = Type::getInt32Ty(Ctx);

  Int8PtrTy  = Type::getInt8PtrTy(Ctx);
  Int16PtrTy = Type::getInt16PtrTy(Ctx);
  Int32PtrTy = Type::getInt32PtrTy(Ctx);
  Int64PtrTy = Type::getInt64PtrTy(Ctx);

  VoidTy = Type::getVoidTy(Ctx);
  

  // Get the function to call from our untime library.
  for (unsigned i = 0; i < FUNCARRAYSIZE; i++) {
    const unsigned ByteSize = 1U << i;
    const unsigned BitSize = ByteSize * 8;
//    errs() << BitSize << "\n";
    std::string ByteSizeStr = utostr(ByteSize);
    std::string BitSizeStr = utostr(BitSize);

    Type *Ty = Type::getIntNTy(Ctx, BitSize);
    Type *PtrTy = Ty->getPointerTo();

    // uint8_t cds_atomic_load8 (void * obj, int atomic_index)
    // void cds_atomic_store8 (void * obj, int atomic_index, uint8_t val)
    SmallString<32> LoadName("cds_load" + BitSizeStr);
    SmallString<32> StoreName("cds_store" + BitSizeStr);
    SmallString<32> AtomicLoadName("cds_atomic_load" + BitSizeStr);
    SmallString<32> AtomicStoreName("cds_atomic_store" + BitSizeStr);

//    CDSLoad[i]  = M.getOrInsertFunction(LoadName, Ty, PtrTy);
//    CDSStore[i] = M.getOrInsertFunction(StoreName, VoidTy, PtrTy, Ty);
    CDSLoad[i]  = M.getOrInsertFunction(LoadName, VoidTy, PtrTy);
    CDSStore[i] = M.getOrInsertFunction(StoreName, VoidTy, PtrTy);
    CDSAtomicLoad[i]  = M.getOrInsertFunction(AtomicLoadName, Ty, PtrTy, OrdTy);
    CDSAtomicStore[i] = M.getOrInsertFunction(AtomicStoreName, VoidTy, PtrTy, OrdTy, Ty);

    for (int op = AtomicRMWInst::FIRST_BINOP; op <= AtomicRMWInst::LAST_BINOP; ++op) {
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
      CDSAtomicRMW[op][i] = M.getOrInsertFunction(AtomicRMWName, Ty, PtrTy, OrdTy, Ty);
    }

    // only supportes strong version
    SmallString<32> AtomicCASName("cds_atomic_compare_exchange" + BitSizeStr);    
    CDSAtomicCAS[i]   = M.getOrInsertFunction(AtomicCASName, Ty, PtrTy, Ty, Ty, OrdTy, OrdTy);
  }

  CDSAtomicThreadFence = M.getOrInsertFunction("cds_atomic_thread_fence", VoidTy, OrdTy);
}

static bool isVtableAccess(Instruction *I) {
  if (MDNode *Tag = I->getMetadata(LLVMContext::MD_tbaa))
    return Tag->isTBAAVtableAccess();
  return false;
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

    initializeCallbacks( *F.getParent() );

    SmallVector<Instruction*, 8> AllLoadsAndStores;
    SmallVector<Instruction*, 8> LocalLoadsAndStores;
    SmallVector<Instruction*, 8> AtomicAccesses;

    std::vector<Instruction *> worklist;

    bool Res = false;
    const DataLayout &DL = F.getParent()->getDataLayout();
  
    errs() << "Before\n";
    F.dump();

    for (auto &B : F) {
      for (auto &I : B) {
        if ( (&I)->isAtomic() ) {
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
//      Res |= instrumentLoadOrStore(Inst, DL);
//      errs() << "load and store are not replaced\n";
    }

    for (auto Inst : AtomicAccesses) {
      Res |= instrumentAtomic(Inst);
    } 

    if (Res) {
      errs() << F.getName(); 
      errs() << " has above instructions replaced\n";
    }
  }
//	  errs() << "After\n";
//	  F.dump();
  
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

  int size = getTypeSize(Addr->getType());
  int index = sizetoindex(size);

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
  OnAccessFunc = IsWrite ? CDSStore[index] : CDSLoad[index];
  
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


bool CDSPass::instrumentAtomic(Instruction * I) {
  IRBuilder<> IRB(I);
  // LLVMContext &Ctx = IRB.getContext();

  if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
    int atomic_order_index = getAtomicOrderIndex(SI->getOrdering());

    Value *val = SI->getValueOperand();
    Value *ptr = SI->getPointerOperand();
    Value *order = ConstantInt::get(OrdTy, atomic_order_index);
    Value *args[] = {ptr, order, val};

    int size=getTypeSize(ptr->getType());
    int index=sizetoindex(size);

    Instruction* funcInst=CallInst::Create(CDSAtomicStore[index], args,"");
    ReplaceInstWithInst(SI, funcInst);
    errs() << "Store replaced\n";
  } else if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
    int atomic_order_index = getAtomicOrderIndex(LI->getOrdering());

    Value *ptr = LI->getPointerOperand();
    Value *order = ConstantInt::get(OrdTy, atomic_order_index);
    Value *args[] = {ptr, order};

    int size=getTypeSize(ptr->getType());
    int index=sizetoindex(size);

    Instruction* funcInst=CallInst::Create(CDSAtomicLoad[index], args, "");
    ReplaceInstWithInst(LI, funcInst);
    errs() << "Load Replaced\n";
  } else if (AtomicRMWInst *RMWI = dyn_cast<AtomicRMWInst>(I)) {
    int atomic_order_index = getAtomicOrderIndex(RMWI->getOrdering());

    Value *val = RMWI->getValOperand();
    Value *ptr = RMWI->getPointerOperand();
    Value *order = ConstantInt::get(OrdTy, atomic_order_index);
    Value *args[] = {ptr, order, val};

    int size = getTypeSize(ptr->getType());
    int index = sizetoindex(size);

    Instruction* funcInst = CallInst::Create(CDSAtomicRMW[RMWI->getOperation()][index], args, "");
    ReplaceInstWithInst(RMWI, funcInst);
    errs() << RMWI->getOperationName(RMWI->getOperation());
    errs() << " replaced\n";
  } else if (AtomicCmpXchgInst *CASI = dyn_cast<AtomicCmpXchgInst>(I)) {
    IRBuilder<> IRB(CASI);

    Value *Addr = CASI->getPointerOperand();

    int size = getTypeSize(Addr->getType());
    int index = sizetoindex(size);
    const unsigned ByteSize = 1U << index;
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
                     order_succ, order_fail};

    CallInst *funcInst = IRB.CreateCall(CDSAtomicCAS[index], Args);
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
    Value *Args[] = {order};

    CallInst *funcInst = CallInst::Create(CDSAtomicThreadFence, Args);
    ReplaceInstWithInst(FI, funcInst);
    errs() << "Thread Fences replaced\n";
  }
  return true;
}



char CDSPass::ID = 0;

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerCDSPass(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
  PM.add(new CDSPass());
}
static RegisterStandardPasses 
	RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,
registerCDSPass);
