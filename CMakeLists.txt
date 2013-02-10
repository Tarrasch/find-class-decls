set(LLVM_USED_LIBS clangTooling)

add_clang_executable(ast-pass ASTPass.cpp)
