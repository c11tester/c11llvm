C11Tester LLVM frontend
=======================

This repository contains the LLVM frontend for instrumenting C/C++
code for the C11Tester framework.

To build this frontend do the following:
1) Clone the repository using git into a folder names CDSPass
2) Obtain a copy of the LLVM compiler
2) Place the CDSPass folder under the directory llvm/lib/Transformation
3) Add "add_subdirectory(CDSPass)" to llvm/lib/Transformation/CMakeLists.txt
4) Build LLVM following the LLVM build instructions
