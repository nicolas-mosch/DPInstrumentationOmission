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
#include "Graph.hpp"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DebugLoc.h"

#include "llvm/IR/IRBuilder.h"

#include <fstream>
// #include "llvm/ADT/Statistic.h"
// #include "llvm/Analysis/MemorySSA.h"
// #include "llvm/Analysis/DependenceAnalysis.h"
// #include "llvm/IR/InstIterator.h"
#define DEBUG_TYPE "dep-analysis"

using namespace std;
using namespace llvm;

STATISTIC(totalInstrCount, "Total Store/Load Instructions");
STATISTIC(omittableInstrCount, "Disregardable Store/Load Instructions");

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
      errs() << "\n---------- ROP Analysis on " << F.getName() <<  " ----------\n";
      errs() << F.getParent()->getSourceFileName() << "\n";

      DebugLoc dl;
      Value* operand;
      string paramName;

      set<Value*> localValues, writtenValues;

      // Get local values (variables)
      for (inst_iterator I = inst_begin(F), SrcE = inst_end(F); I != SrcE; ++I) {
        if (DbgDeclareInst* DbgDeclare = dyn_cast<DbgDeclareInst>(&*I)) {
          localValues.insert(DbgDeclare->getAddress());
        } else if (DbgValueInst* DbgValue = dyn_cast<DbgValueInst>(&*I)) {
          localValues.insert(DbgValue->getValue());
        }else if(isa<StoreInst>(&*I)){
          if(I->getDebugLoc()){
            writtenValues.insert(I->getOperand(1));
          }
        }
      }

      set<Instruction*> omittableInstructions;

      for (inst_iterator I = inst_begin(F), SrcE = inst_end(F); I != SrcE; ++I) {
        if(isa<StoreInst>(&*I) || isa<LoadInst>(&*I)){
          ++totalInstrCount;
          dl = I->getDebugLoc();
          Value *v = I->getOperand(isa<StoreInst>(&*I) ? 1 : 0);
          if(
            !dl 
            || (
              localValues.find(v) != localValues.end() 
              && writtenValues.find(v) == writtenValues.end()
            ) 
            // || v->getName() == "retval"
          ){
            omittableInstructions.insert(&*I);
          }
        }
      }
    
      omittableInstrCount += omittableInstructions.size();


      ofstream stream;
      stream.open("ignoring_intructions.txt", ios_base::app);
      if (stream.is_open())
      {
        errs() << "Omittable Instructions:\n";
        for(auto I : omittableInstructions){
          errs() << "\t" << (isa<StoreInst>(I) ? "Write " : "Read ") << getVarName(&*I) << " | ";
          if(dl = I->getDebugLoc()){
            errs() << dl.getLine() << "," << dl.getCol() << " | " << I->getName() << "\n";
          }else{
            errs() << "INIT\n";
          }
          stream
              << (isWrite ? "w" : "r")
              << "|" << I->getOperand(isWrite ? 1 : 0)->getName().str()
              << "|" << dl.getLine()
              << "|" << dl.getCol()
              << "\n"
            ;
        }
      }else{
        errs() << "Problem opening file: ignoring_intructions.txt\n";
      }

      return false;
    }

    
    string getVarName(Instruction *I){
      /*
      if(isa<AllocaInst>(I)){
        Instruction *K = I->getNextNonDebugInstruction();
        while(K = K->getNextNonDebugInstruction()){
          if(isa<StoreInst>(K) && ((Instruction*)K->getOperand(1)) == I){
            return K->getOperand(0)->getName();
          }
        }
        return "n/a";
      }*/
      
      if(isa<StoreInst>(I) || isa<LoadInst>(I)){
        string r;
        Value *v = I->getOperand(isa<StoreInst>(I) ? 1 : 0);
        if(v->hasName()){
          string r = v->getName().str();
          std::size_t found = r.find(".addr");
          if(found != string::npos){
            return r.erase(found);
          }
          return r;
        }else{
          return "*" + getVarName((Instruction*)v);
        }
      }
      return "n/a";
    }


    bool isArrayAccess(Instruction* I) {
      for(Type* subType : I->getOperand(isa<StoreInst>(I) ? 1 : 0)->getType()->subtypes()){
        if(subType->isArrayTy())
          return true;
      }
      return false;
    }

    bool isPtrAccess(Instruction* I) {
      if(I->getOperand(isa<StoreInst>(I) ? 1 : 0)->getType()->isPointerTy())
        return true;
      for(Type* subType : I->getOperand(isa<StoreInst>(I) ? 1 : 0)->getType()->subtypes()){
        if(subType->isPointerTy())
          return true;
      }
      return false;
    }

  };
}

char DepAnalysis::ID = 0;

static RegisterPass<DepAnalysis> X("dep-analysis", "Run the DepAnalysis algorithm. Generates a dependence graph", false, false);
//static cl::opt<bool, false> printToDot("printToDot", cl::desc("Print dot file containing the depgraph"), cl::NotHidden);
