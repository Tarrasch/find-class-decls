#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"

#include "clang/Analysis/CFG.h"
#include "clang/Analysis/CallGraph.h"
#include "clang/Frontend/FrontendActions.h"

#include "stdio.h"
#include <iostream>
#include <set>
#include <queue>
#include <algorithm>

#define all(c) c.begin(), c.end()

using namespace clang;
using namespace std;

class ASTPassClassVisitor
  : public RecursiveASTVisitor<ASTPassClassVisitor> {
public:
  explicit ASTPassClassVisitor(ASTContext *context)
    : context(context) {
    numFunctions = 0;
  }

  int numFunctions;

  typedef pair<bool, Expr*> P;
  typedef vector<P> VP;

  VP linearize(Expr *e){
    VP vec;
    if(isa<BinaryOperator>(e)) {
      BinaryOperator *bo = (BinaryOperator*)e;
      // Is binary operator, act recursively
      VP vp1 = linearize(bo->getLHS());
      VP vp2 = linearize(bo->getRHS());
      vec.insert(vec.end(), all(vp1));
      vec.insert(vec.end(), all(vp2));
    } else {
      vec.push_back(P(!isa<IntegerLiteral>(e), e));
    }
    return vec;
  }

  void rewriteAddition(BinaryOperator *bo){
    if(bo->getOpcode() == BO_Add){
      cout << "!! BEFORE !!" << endl; bo->dumpAll();
      cout << "Rewriting started ..." << endl;
      VP vec = linearize(bo);
      stable_sort(all(vec));

      bo->setRHS(vec.back().second);
      vec.pop_back();

      Expr *l = vec.front().second;
      vec.erase(vec.begin());

      while(!vec.empty()){
        Expr *next = vec.front().second;
        vec.erase(vec.begin());
        l = new (context) BinaryOperator(l, next, BO_Add, bo->getType(), bo->getValueKind(), bo->getObjectKind(), bo->getExprLoc());
      }
      bo->setLHS(l);

      cout << "!! AFTER !!" << endl; bo->dumpAll();
      cout << endl << endl;
    }
  }

  bool VisitBinaryOperator(BinaryOperator *bo){
    cout << (bo->getOpcode() == BO_Add ? "Addition" : "Not addition") << endl;

    rewriteAddition(bo);

    return true;
  }

  bool VisitFunctionDecl(FunctionDecl  *decl) {
    numFunctions++;
    string fname = decl->getNameInfo().getAsString();
    cout << fname << endl;

    if(!decl->hasBody()){
      cout << "no body :(" << endl;
    }
    else {
      // Create CFG
      Stmt *body = decl->getBody();
      CFG::BuildOptions bo;
      CFG *cfg = CFG::buildCFG(decl, body, &decl->getASTContext(), bo);

      // Pretty print CFG
      LangOptions lo;
      cfg->dump(lo, true);

      // 3. # Num basic blocks in this function
      int num_basicblocks = cfg->getNumBlockIDs();
      cout << "Total number of basics blocks for function " << fname << ": " << num_basicblocks << endl;

      // 4. # Num basic block edges in this function
      for (CFG::const_iterator I = cfg->begin(), E = cfg->end() ; I != E ; ++I) {
        // Skip the entry block, because we already printed it.
        cout << "SCOOBYDOO" << endl;
        const CFGBlock &B(**I);


        int num_succs = B.succ_size();
        cout << "Block " << B.getBlockID() << " has " << num_succs << " successor edges!" << endl;

        for (CFGBlock::const_succ_iterator succ_I = B.succ_begin(), succ_E = B.succ_end();
            succ_I != succ_E; ++succ_I){
          cout << "\tDoobyScoo" << endl;
        }
      }


      // 5. # Num unreachable basic blocks
      // We just do simple bfs on our own
      set<CFGBlock*> visited;
      queue<CFGBlock*> q;
      q.push(&cfg->getEntry());
      while(!q.empty()) {
        CFGBlock *B(q.front()); q.pop();
        if(!visited.count(B)){
          visited.insert(B);
          for (CFGBlock::succ_iterator succ_I = B->succ_begin(), succ_E = B->succ_end();
              succ_I != succ_E; ++succ_I){
            q.push(&(**succ_I));
          }
        }
      }
      int num_reachable = visited.size();
      int num_unreachable = num_basicblocks - num_reachable;

      // Now collect data for the end
      cout << "Number of unreachable blocks " << num_unreachable << endl;
    }
    return true;
  }

  bool VisitCXXRecordDecl(CXXRecordDecl *Declaration) {
    if (Declaration->getQualifiedNameAsString() == "n::m::C") {
      FullSourceLoc FullLocation = context->getFullLoc(Declaration->getLocStart());
      if (FullLocation.isValid())
        llvm::outs() << "Found declaration at "
                     << FullLocation.getSpellingLineNumber() << ":"
                     << FullLocation.getSpellingColumnNumber() << "\n";
    }
    return true;
  }

  void printStats() {
    // 1.
    cout << "Number of functions: " << numFunctions << endl;

    // 2.
  }

private:
  ASTContext *context;
};

class MyCallGraph
  : public CallGraph {
public:
  explicit MyCallGraph() {
    totalEdges = 0;
  }

  int totalEdges;

  void printStats() {
    raw_ostream &OS(llvm::errs());
    for (const_iterator I = begin(), E = end(); I != E; ++I) {
      if (I->second == getRoot())
        OS << "< root >";
      else
        I->second->print(OS);
      OS << " calls: ";
      for (CallGraphNode::iterator CI = I->second->begin(),
          CE = I->second->end(); CI != CE; ++CI) {
        assert(*CI != getRoot() && "No one can call the root node.");
        (*CI)->print(OS);
        OS << " ";
      }
      OS << I->second->size() << '\n';
      totalEdges += I->second->size();
    }
    OS.flush();

    cout << "Total number of edges: " << totalEdges << endl;
    /* for(const_iterator it = begin();;) { } */
  }

/*   virtual bool VisitDecl(Decl *decl) { */
/*     return true; */
/*   } */
};

class ASTPassClassConsumer : public clang::ASTConsumer {
  public:
    explicit ASTPassClassConsumer(ASTContext *context)
      : visitor(context) {}

    virtual void HandleTranslationUnit(clang::ASTContext &context) {
      visitor.TraverseDecl(context.getTranslationUnitDecl());
      visitor.printStats();
      callgraph.TraverseDecl(context.getTranslationUnitDecl());
      callgraph.dump();
      callgraph.printStats();
    }
  private:
    ASTPassClassVisitor visitor;
    MyCallGraph callgraph;
};

class ASTPassClassAction : public clang::ASTFrontendAction {
  public:
    virtual clang::ASTConsumer *CreateASTConsumer(
        clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
      return new ASTPassClassConsumer(&Compiler.getASTContext());
    }
};

int main(int argc, char **argv) {
  if (argc > 1) {
    Twine tw(argv[1]);
    clang::tooling::runToolOnCode(new ASTPassClassAction, tw);
    cout << "\n\n\n\n" << endl;
    clang::tooling::runToolOnCode(new ASTDumpAction, tw);
  }
}
