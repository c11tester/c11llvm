bool containsStr() {

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
		Value *args[] = {ptr, val};

		Instruction* funcInst=CallInst::Create(CDSAtomicInit[Idx], args,"");
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
		Value *args[] = {ptr, order};
		
		Instruction* funcInst=CallInst::Create(CDSAtomicLoad[Idx], args,"");
		ReplaceInstWithInst(CI, funcInst);

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
		Value *args[] = {ptr, val, order};
		
		Instruction* funcInst=CallInst::Create(CDSAtomicStore[Idx], args,"");
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
		Value *args[] = {ptr, val, order};
		
		Instruction* funcInst=CallInst::Create(CDSAtomicRMW[op][Idx], args,"");
		ReplaceInstWithInst(CI, funcInst);

		return true;
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
									order_succ, order_fail};
		
		Instruction* funcInst=CallInst::Create(CDSAtomicCAS_V2[Idx], args,"");
		ReplaceInstWithInst(CI, funcInst);

		return true;
	}

	return false;
}
