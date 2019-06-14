void CDSPass::initializeCallbacks(Module &M) {
	LLVMContext &Ctx = M.getContext();

	Type * Int1Ty = Type::getInt1Ty(Ctx);
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
		CDSAtomicInit[i] = M.getOrInsertFunction(AtomicInitName, VoidTy, PtrTy, Ty);
		CDSAtomicLoad[i]  = M.getOrInsertFunction(AtomicLoadName, Ty, PtrTy, OrdTy);
		CDSAtomicStore[i] = M.getOrInsertFunction(AtomicStoreName, VoidTy, PtrTy, Ty, OrdTy);

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
			CDSAtomicRMW[op][i] = M.getOrInsertFunction(AtomicRMWName, Ty, PtrTy, Ty, OrdTy);
		}

		// only supportes strong version
		SmallString<32> AtomicCASName_V1("cds_atomic_compare_exchange" + BitSizeStr + "_v1");
		SmallString<32> AtomicCASName_V2("cds_atomic_compare_exchange" + BitSizeStr + "_v2");
		CDSAtomicCAS_V1[i] = M.getOrInsertFunction(AtomicCASName_V1, 
								Ty, PtrTy, Ty, Ty, OrdTy, OrdTy);
		CDSAtomicCAS_V2[i] = M.getOrInsertFunction(AtomicCASName_V2, 
								Int1Ty, PtrTy, PtrTy, Ty, OrdTy, OrdTy);
	}

	CDSAtomicThreadFence = M.getOrInsertFunction("cds_atomic_thread_fence", VoidTy, OrdTy);
}