#pragma once

#include <llvm/IR/DebugLoc.h>
//#include <llvm/IR/Constant.h>
//#include <llvm/IR/Instruction.h>
//#include <llvm/IR/IRBuilder.h>
//#include <llvm/Support/raw_ostream.h>

Value *getPosition( Instruction * I, IRBuilder <> IRB)
{
	const DebugLoc & debug_location = I->getDebugLoc ();
	std::string position_string;
	{
		llvm::raw_string_ostream position_stream (position_string);
		debug_location . print (position_stream);
	}

	return IRB . CreateGlobalStringPtr (position_string);
}

Value *getPositionPrint( Instruction * I, IRBuilder <> IRB)
{
	const DebugLoc & debug_location = I->getDebugLoc ();
	std::string position_string;
	{
		llvm::raw_string_ostream position_stream (position_string);
		debug_location . print (position_stream);
	}
	errs() << position_string << "\n";
	return IRB . CreateGlobalStringPtr (position_string);
}