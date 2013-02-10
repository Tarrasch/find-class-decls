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
#include <numeric>


using namespace clang;
using namespace std;

#define all(c) c.begin(), c.end()
typedef vector < int > VI;

float avg(VI v) { return (accumulate(all(v), 0)+0.0)/v.size(); }
void minMaxAvg(VI v, string desc) {
  cout << "Minimum " << desc << ": " << *min_element(all(v)) << endl;
  cout << "Maximum " << desc << ": " << *max_element(all(v)) << endl;
  cout << "Average " << desc << ": " << avg(v) << endl;
  cout << endl;
}

// Only for task A1
class MyCallGraph
: public CallGraph {
  public:
    explicit MyCallGraph() {
      numFunctions = 0;
    }

    int numFunctions;

    bool VisitFunctionDecl(FunctionDecl  *decl) {
      numFunctions++;
      return true;
    }

    int calcTotalEdges() {
      int totalEdges = 0;
      for (const_iterator I = begin(), E = end(); I != E; ++I) {
        for (CallGraphNode::iterator CI = I->second->begin(),
            CE = I->second->end(); CI != CE; ++CI) {
          assert(*CI != getRoot() && "No one can call the root node.");
        }
        totalEdges += I->second->size();
      }
      return totalEdges;
    }

    void printStats() {
      cout << "Number of functions: " << numFunctions << endl;
      cout << "Total number of edges: " << calcTotalEdges() << endl;
    }

};

// Only for question A2
class ASTNodeCounter
  : public RecursiveASTVisitor<ASTNodeCounter> {
    public:
    ASTNodeCounter(){ total = 0; }
    int total;
    set < void* > my_set;

    bool VisitType(Type *p){my_set.insert((void*)p);total++; return true;}
    bool VisitDecl(Decl *p){my_set.insert((void*)p);total++; return true;}
    bool VisitDeclContext(DeclContext *p){my_set.insert((void*)p);total++; return true;}
    bool VisitStmt(Stmt *p){my_set.insert((void*)p);total++; return true;}

    int totalNumberOfNodes() { return my_set.size(); }
    void printStats() {
      cout << "Ok I found " << totalNumberOfNodes() << " AST nodes in total" << endl;
    }
};

// Most important one, A3, A4, A5 and partially A2
class ASTPassClassVisitor
  : public RecursiveASTVisitor<ASTPassClassVisitor> {
public:
  explicit ASTPassClassVisitor(ASTContext *context)
    : context(context) { }

  VI astNodes, blocks, cfgEdges, unreachables;

  bool VisitFunctionDecl(FunctionDecl  *decl) {
    string fname = decl->getNameInfo().getAsString();
    cout << fname << endl;

    if(!decl->hasBody()){
      return true;
    }
    // Create CFG
    Stmt *body = decl->getBody();
    CFG::BuildOptions bo;
    CFG *cfg = CFG::buildCFG(decl, body, &decl->getASTContext(), bo);

    // Pretty print CFG
    /* LangOptions lo; */
    /* cfg->dump(lo, true); */

    // 3. # Num basic blocks in this function
    const int num_basicblocks = cfg->getNumBlockIDs();
    cout << "Total number of basics blocks for function " << fname << ": " << num_basicblocks << endl;

    // 4. # Num basic block edges in this function
    int tot_edges = 0;
    for (CFG::const_iterator I = cfg->begin(), E = cfg->end() ; I != E ; ++I) {
      // Skip the entry block, because we already printed it.
      const CFGBlock &B(**I);


      int num_succs = B.succ_size();
      cout << "Block " << B.getBlockID() << " has " << num_succs << " successor edges!" << endl;
      tot_edges += num_succs;

      for (CFGBlock::const_succ_iterator succ_I = B.succ_begin(), succ_E = B.succ_end();
          succ_I != succ_E; ++succ_I){
        // Just showing that it's traverseable
      }
    }
    const int tot_cfgEdges = tot_edges;


    // 5. # Num unreachable basic blocks
    // We just do simple bfs by ourselves ...
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
    const int num_unreachable = num_basicblocks - num_reachable;

    // Now collect data for the end
    cout << "Number of unreachable blocks " << num_unreachable << endl;

    ASTNodeCounter nc;
    nc.TraverseDecl(decl);

    astNodes.push_back(nc.totalNumberOfNodes());
    blocks.push_back(num_basicblocks);
    cfgEdges.push_back(tot_cfgEdges);
    unreachables.push_back(num_unreachable);
    return true;
  }

  void printStats() {
    minMaxAvg(astNodes, "number of AST nodes");
    minMaxAvg(blocks, "number of basic blocks");
    minMaxAvg(cfgEdges, "total number of cfg-edges");
    minMaxAvg(unreachables, "total number of unreachable blocks");
  }

private:
  ASTContext *context;
};

// Only for question B
class PlusReassociator
  : public RecursiveASTVisitor<PlusReassociator> {
public:
  explicit PlusReassociator(ASTContext *context)
    : context(context) {
  }

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

      // Just to make sure we don't visit the children (for pretty printing
      // purposes) lets destroy the AST structure
      bo->setLHS(bo->getRHS());
    }
  }

  bool VisitBinaryOperator(BinaryOperator *bo){
    rewriteAddition(bo);
    return true;
  }
private:
  ASTContext *context;
};

class ASTPassClassConsumer : public clang::ASTConsumer {
  public:
    explicit ASTPassClassConsumer(ASTContext *context)
      : visitor(context), pr(context) {}

    virtual void HandleTranslationUnit(clang::ASTContext &context) {
      visitor.TraverseDecl(context.getTranslationUnitDecl());
      visitor.printStats();
      callgraph.TraverseDecl(context.getTranslationUnitDecl());
      /* callgraph.dump(); */
      callgraph.printStats();
      pr.TraverseDecl(context.getTranslationUnitDecl());
    }
  private:
    ASTPassClassVisitor visitor;
    MyCallGraph callgraph;
    PlusReassociator pr;
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
    /* cout << "\n\n\n\n" << endl; */
    /* clang::tooling::runToolOnCode(new ASTDumpAction, tw); */
  }
}
