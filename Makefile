all: lib
	cabal v2-configure
	cabal v2-build
	cp ./dist-newstyle/build/x86_64-linux/ghc-8.6.4/latte-compiler-0.1.0.0/x/latte-compiler/build/latte-compiler/latte-compiler ./latc
	cp ./latc ./latc_llvm

lib:lib/runtime.ll
	llvm-as -o ./lib/runtime.bc ./lib/runtime.ll