//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//


#include "llvm/Support/CommandLine.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/DominanceFrontier.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "PDG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DebugLoc.h"

#include "llvm/IR/IRBuilder.h"

// #include "llvm/ADT/Statistic.h"
// #include "llvm/Analysis/MemorySSA.h"
// #include "llvm/Analysis/DependenceAnalysis.h"
// #include "llvm/IR/InstIterator.h"
#define DEBUG_TYPE "dep-analysis"

using namespace std;
using namespace llvm;

namespace {
  struct DepAnalysis : public FunctionPass {
    static char ID;
    DependenceInfo *DI;
    LoopInfo *LI;
    PDG *DG, *CFG;

    DepAnalysis() : FunctionPass(ID) {}

    void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
      
      //AU.addRequired<PostDominatorTree>();
      AU.addRequired<DependenceAnalysisWrapperPass>();
      //AU.addRequired<DominanceFrontier>();
      AU.addRequired<LoopInfoWrapperPass>();
      //AU.addRequired<RegionInfoPass>();
    }

    bool runOnFunction(Function &F) {
      errs() << "DepAnalysis on " << F.getName() << "\n";

      //LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
      //RegionInfo &RI = getAnalysis<RegionInfoPass>().getRegionInfo();

      //auto &PDT = getAnalysis<PostDominatorTree>();
      DebugLoc dl;
      
      // Create Load/Store-Instruction-CFG

      CFG = new PDG(F.getName(), &F);
      
      for (inst_iterator I = inst_begin(F), SrcE = inst_end(F); I != SrcE; ++I) {
          if((&*I)->getDebugLoc() && (isa<StoreInst>(*I) || isa<LoadInst>(*I))){
              CFG->addNode(&*I);
          }
      }
      
      errs() << "Building CFG\n";
      std::function<void(BasicBlock*,Instruction*)> add_first_successor_store_load_instructions;
      add_first_successor_store_load_instructions = [&](BasicBlock *BB, Instruction* previousInstruction) 
      {
        for (BasicBlock *S : successors(BB)) {
          for (Instruction &I : *S){
            DebugLoc dl = I.getDebugLoc();
            if(dl && (isa<StoreInst>(I) || isa<LoadInst>(I))){
              CFG->addEdge(previousInstruction, &I, EdgeDepType::CTR);
              goto next;
            }
          }
          add_first_successor_store_load_instructions(S, previousInstruction);
          next:;
        }
      };

      Instruction *previousInstruction;
      for (BasicBlock &BB : F){
        // Add current block's store/load-instructions to graph
        previousInstruction = nullptr;
        for (Instruction &I : BB){
          dl = I.getDebugLoc();
          if(dl && (isa<StoreInst>(I) || isa<LoadInst>(I))){
            if(previousInstruction != nullptr){
                CFG->addEdge(previousInstruction, &I, EdgeDepType::CTR);
            }
            previousInstruction = &I;
          }
        }
        // Add edges from last instruction in current block to first instruction all the successor blocks
        if(previousInstruction != nullptr){
          add_first_successor_store_load_instructions(&BB, previousInstruction);
        }
      }
      
      for(auto node : CFG->getNodes()){
        if(node != CFG->getEntry() && node != CFG->getExit()){
          if(CFG->getInEdges(node).empty()){
            CFG->connectToEntry(node->getItem());
          }
          if(CFG->getOutEdges(node).empty()){
            CFG->connectToExit(node->getItem());
          }
        }
      }
      
      CFG->dumpToDot(F.getName().str() + "_cfg.dot");
      
      errs() << "Building Dep-Graph\n";
      // Create Dependence Graph
      DI = &getAnalysis<DependenceAnalysisWrapperPass>().getDI();
	    LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();

      DG = new PDG(F.getName(), &F);

      map<string, DIScope*> declareMap;
	    string varNameSrc, varNameDst;
    
      // Get declaration locs and add all store/load-instructions to graph
      vector<string> possibleFPVs;
      for (inst_iterator I = inst_begin(F), SrcE = inst_end(F); I != SrcE; ++I) {
        dl = (&*I)->getDebugLoc();
        if(dl){
          if(isa<StoreInst>(&*I) || isa<LoadInst>(&*I)){
            DG->addNode(&*I);
            if(isa<StoreInst>(&*I) && LI->getLoopFor((*I).getParent())){
              possibleFPVs.push_back((*I).getOperand(1)->getName().str());
            }
          }
          auto *s = cast<DIScope>(dl.getScope());
          if (DbgDeclareInst* DbgDeclare = dyn_cast<DbgDeclareInst>(&*I)) {
            declareMap[DbgDeclare->getAddress()->getName().str()] = s;
          } else if (DbgValueInst* DbgValue = dyn_cast<DbgValueInst>(&*I)) {
            declareMap[DbgValue->getValue()->getName().str()] = s;
          }
        }
      }
      
      errs() << "possibleFPVs: [";
      for(string s : possibleFPVs){
        errs() << s << ", ";
      }

      errs() << "]\n";



      recursiveDepFinder();

      DG->dumpToDot(F.getName().str() + "_deps.dot");
      
      // Remove possible false positives
      /*
      Instruction *src, *dst;
      for(auto edge : DG->getEdges()){
        src = edge->getSrc()->getItem();
        dst = edge->getDst()->getItem();
        
        if(src != nullptr){
          auto *op = src->getOperand(isa<StoreInst>(src) ? 1 : 0);

          if(
              find(
                possibleFPVs.begin(),
                possibleFPVs.end(),
                op->getName().str()
              ) != possibleFPVs.end()
              || isa<GlobalVariable>(*op)
              || isa<GetElementPtrInst>(*op)
           ){
             errs() << "Removing edge " << DG->getNodeIndex(src) << " -> " << DG->getNodeIndex(src) << "\n";
             DG->removeEdge(edge);
          }
        }
      }
      */

      DG->dumpToDot(F.getName().str() + "_deps2.dot");
      
      errs() << "done2\n";
      return false;
    }

    void recursiveDepFinder(){
      errs() << "recursiveDepFinder\n";
      vector<Instruction*>* checkedInstructions = new vector<Instruction*>();
      for(auto edge: CFG->getInEdges(CFG->getExit())){
        recursiveDepFinderHelper1(checkedInstructions, edge->getSrc()->getItem());
      }
    }

    bool recursiveDepFinderHelper1(vector<Instruction*>* checkedInstructions, Instruction* I){
      errs() << "Checking dependencies for " << CFG->getNodeIndex(I) << "\n";
      checkedInstructions->push_back(I);
      for(auto edge: CFG->getInEdges(I)){
        recursiveDepFinderHelper2(new vector<Instruction*>(), I, edge->getSrc()->getItem());
        if(find(checkedInstructions->begin(), checkedInstructions->end(), edge->getSrc()->getItem()) == checkedInstructions->end()){
          recursiveDepFinderHelper1(checkedInstructions, edge->getSrc()->getItem());
        }
      }
    }

    void recursiveDepFinderHelper2(vector<Instruction*>* checkedInstructions, Instruction* I, Instruction* C){
      checkedInstructions->push_back(C);
      if(CFG->getNode(C) == CFG->getEntry()){
        return;
      }
      errs() << "\t" << CFG->getNodeIndex(C) <<": ";

      if(auto D = DI->depends(C, I, true)){
        string varNameSrc = I->getOperand(isa<StoreInst>(I) ? 1 : 0)->getName().str();
        string varNameDst = C->getOperand(isa<StoreInst>(C) ? 1 : 0)->getName().str();
        if(varNameSrc == varNameDst){
          if (D->isOutput())
          {
              DG->addEdge(I, C, EdgeDepType::WAW);
              errs() << "WAW";
          }
          else if (D->isFlow())
          {
              DG->addEdge(I, C, EdgeDepType::RAW);
              errs() << "RAW";
          }
          else if (D->isAnti())
          {
              DG->addEdge(I, C, EdgeDepType::WAR);
              errs() << "WAR";
          }else{
            errs() << "RAR\n";
            return;
          }
          if(
            (LI->getLoopFor((*C).getParent()) || LI->getLoopFor((*I).getParent()))
              && (*C).getParent() != (*I).getParent()
          ){
            errs() << " (boundary dep)" ;
          }
          errs() << "\n";
        }
      }else{
        errs() << "none\n";
      }
      for(auto edge: CFG->getInEdges(C)){
        if(find(checkedInstructions->begin(), checkedInstructions->end(), edge->getSrc()->getItem()) == checkedInstructions->end()){
          recursiveDepFinderHelper2(checkedInstructions, I, edge->getSrc()->getItem());
        }
      }
    }
  };
}

char DepAnalysis::ID = 0;

static RegisterPass<DepAnalysis> X("dep-analysis", "Run the DepAnalysis algorithm. Generates a dependence graph", false, false);
//static cl::opt<bool, false> printToDot("printToDot", cl::desc("Print dot file containing the depgraph"), cl::NotHidden);
