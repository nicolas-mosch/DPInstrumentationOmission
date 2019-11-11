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
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/IRBuilder.h"

#include <fstream>
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/IR/InstIterator.h"
#define DEBUG_TYPE "dep-analysis"

using namespace std;
using namespace llvm;

STATISTIC(totalInstrCount, "Total Store/Load Instructions");
STATISTIC(omittableInstrCount, "Disregardable Store/Load Instructions");

namespace {
  struct DepAnalysis : public FunctionPass {
    static char ID;

    DepAnalysis() : FunctionPass(ID) {}

    void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
      
      // AU.addRequired<PostDominatorTree>();
      // AU.addRequired<DominanceFrontier>();
      AU.addRequired<RegionInfoPass>();
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
          
          errs() << "\t" << (isa<StoreInst>(&*I) ? "Write " : "Read ") << getVarName(&*I) << " | ";
          if(dl = I->getDebugLoc()){
            errs() << dl.getLine() << "," << dl.getCol() << " | " << I->getName();
          }else{
            errs() << "INIT";
          }

          if(
            !dl 
            || (
              localValues.find(v) != localValues.end() 
              && writtenValues.find(v) == writtenValues.end()
            ) 
            // || v->getName() == "retval"
          ){
            omittableInstructions.insert(&*I);
            errs() << " | (OMIT)";
          }

          errs() << "\n";
        }
      }
    
      omittableInstrCount += omittableInstructions.size();

      /*
      errs() << "Omittable Instructions:\n";
      for(auto I : omittableInstructions){
        errs() << "\t" << (isa<StoreInst>(I) ? "Write " : "Read ") << getVarName(&*I) << " | ";
        if(dl = I->getDebugLoc()){
          errs() << dl.getLine() << "," << dl.getCol() << " | " << I->getName() << "\n";
        }else{
          errs() << "INIT\n";
        }
      }
      */
      

      return false;
    }

    
    string getVarName(Instruction *I){
      if(isa<AllocaInst>(I)){
        Value *v = (Value*)I;
        if(v->hasName()){
          string r = v->getName().str();
          std::size_t found = r.find(".addr");
          if(found != string::npos){
            return r.erase(found);
          }
          return r;
        }
        return "!";
      }

      if(isa<GetElementPtrInst>(I)){
        return getVarName((Instruction*)I->getOperand(0)) + "[" + getVarName((Instruction*)I->getOperand(1)) + "]";
      }

      if(isa<SExtInst>(I)){
        return getVarName((Instruction*)I->getOperand(0));
      }
      
      if(isa<StoreInst>(I) || isa<LoadInst>(I)){
        string r;
        Value *v = I->getOperand(isa<StoreInst>(I) ? 1 : 0);
        if(v->hasName()){
         return getVarName((Instruction*)v);
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

// INITIALIZE_PASS(DepAnalysis, "DepAnalysis", "BATMAN", false, false)
static RegisterPass<DepAnalysis> X("dep-analysis", "Run the DepAnalysis algorithm. Generates a dependence graph", false, false);
//static cl::opt<bool, false> printToDot("printToDot", cl::desc("Print dot file containing the depgraph"), cl::NotHidden);

// INITIALIZE_PASS(DepAnalysis, "dep-analysis", "Find omittable instructions",  false, false)
