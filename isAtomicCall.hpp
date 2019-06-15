#pragma once

void printArgs(CallInst *);

bool isAtomicCall(Instruction *I)
{
	if ( auto *CI = dyn_cast<CallInst>(I) ) {
		Function *fun = CI->getCalledFunction();
		if (fun == NULL)
			return false;

		StringRef funName = fun->getName();

		if ( (CI->isTailCall() && funName.contains("atomic_")) ||
			funName.contains("atomic_compare_exchange_") ) {
			// printArgs(CI);
			return true;
		}
	}

	return false;
}

void printArgs (CallInst *CI)
{
	Function *fun = CI->getCalledFunction();
	StringRef funName = fun->getName();

	User::op_iterator begin = CI->arg_begin();
	User::op_iterator end = CI->arg_end();

	if ( funName.contains("atomic_") ) {
		std::vector<Value *> parameters;

		for (User::op_iterator it = begin; it != end; ++it) {
			Value *param = *it;
			parameters.push_back(param);
			errs() << *param << " type: " << *param->getType()  << "\n";
		}
	}

}
