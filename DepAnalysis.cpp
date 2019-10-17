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

#include <fstream>
// #include "llvm/ADT/Statistic.h"
// #include "llvm/Analysis/MemorySSA.h"
// #include "llvm/Analysis/DependenceAnalysis.h"
// #include "llvm/IR/InstIterator.h"
#define DEBUG_TYPE "dep-analysis"

using namespace std;
using namespace llvm;

STATISTIC(instrCount, "Total Store/Load Instructions");
STATISTIC(iinstrCount, "Disregardable Store/Load Instructions");

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
      /*
      if(F.getName() != "fft_twiddle_gen1"){
        return false;
      }
      */
      errs() << "\n---------- DepAnalysis on " << F.getName() << " ----------\n";

      //LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
      //RegionInfo &RI = getAnalysis<RegionInfoPass>().getRegionInfo();

      //auto &PDT = getAnalysis<PostDominatorTree>();
      DebugLoc dl;
      
      errs() << "\tBuilding DepGraph\n";
      DI = &getAnalysis<DependenceAnalysisWrapperPass>().getDI();
	    LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();

      DG = new PDG(F.getName(), &F);

      map<string, bool> declareMap;
	    string varNameSrc, varNameDst;

      CFG = new PDG(F.getName(), &F);
      
      // Get declaration locs and add all store/load-instructions to graph
      vector<string> possibleFPVs;
      set<Value*> unsafeOperands;
      Value* operand;
      string varName;
      for (inst_iterator I = inst_begin(F), SrcE = inst_end(F); I != SrcE; ++I) {
        dl = (&*I)->getDebugLoc();
        if(dl){
          if(CallInst* call_inst = dyn_cast<CallInst>(&*I)){
            Function* fn = call_inst->getCalledFunction();
            for(int i = 0; i < call_inst->getNumOperands() - 1; ++i){
              operand = call_inst->getArgOperand(i);
              errs() << *(operand->getType()) << " " << operand->getName().str();
              if(!isSafe(operand->getType())){
                unsafeOperands.insert(operand);
              }
            }
          }else if(isa<StoreInst>(&*I) || isa<LoadInst>(&*I)){
            DG->addNode(&*I);
            CFG->addNode(&*I);
            if(isa<StoreInst>(&*I) && LI->getLoopFor((*I).getParent())){
              possibleFPVs.push_back((*I).getOperand(1)->getName().str());
            }
          }
          if (DbgDeclareInst* DbgDeclare = dyn_cast<DbgDeclareInst>(&*I)) {
            //declareMap[DbgDeclare->getAddress()->getName().str()] = s;
            declareMap[DbgDeclare->getAddress()->getName().str()] = false;
            varName = DbgDeclare->getAddress()->getName().str();
          } else if (DbgValueInst* DbgValue = dyn_cast<DbgValueInst>(&*I)) {
            //declareMap[DbgValue->getValue()->getName().str()] = s;
            varName = DbgValue->getValue()->getName().str();
          }else{
            continue;
          }
          CFG->addNode(&*I);
          declareMap[varName] = false;
          // errs() << varName << ": " << dl.getLine() << "|" << dl.getCol() << "\n";
        }
      }

      std::function<void(BasicBlock*,Instruction*)> add_first_successor_store_load_instructions;
      add_first_successor_store_load_instructions = [&](BasicBlock *BB, Instruction* previousInstruction) 
      {
        for (BasicBlock *S : successors(BB)) {
          for (Instruction &I : *S){
            DebugLoc dl = I.getDebugLoc();
            if(!dl) continue;
            if(isa<StoreInst>(I) || isa<LoadInst>(I)){
              CFG->addEdge(previousInstruction, &I, EdgeDepType::CTR);
              goto next;
            }else if(DbgDeclareInst* DbgDeclare = dyn_cast<DbgDeclareInst>(&I)){
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
        // errs() << BB.getName() << "\n";
        // Add current block's store/load-instructions to graph
        previousInstruction = nullptr;
        for (Instruction &I : BB){
          dl = I.getDebugLoc();
          if(!dl) continue;
          DbgDeclareInst* DbgDeclare = dyn_cast<DbgDeclareInst>(&I);
          if(isa<StoreInst>(I) || isa<LoadInst>(I) || DbgDeclare){
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
      
      // Conect exit nodes
      for(auto node : CFG->getNodes()){
        if(node != CFG->getEntry() && node != CFG->getExit()){
          if(CFG->getInEdges(node).empty()){
            CFG->connectToEntry(node->getItem());
          }else if(
            CFG->getInEdges(node).size() == 1
            && node->getItem()->getParent()->getName().find("for.cond") != string::npos
          ){
            CFG->connectToExit(node->getItem());
          }
          else if(CFG->getOutEdges(node).empty()){
            CFG->connectToExit(node->getItem());
          }else if(
            CFG->getOutEdges(node).size() == 1
            && node->getItem()->getParent()->getName().find("for.inc") != string::npos
          ){
            CFG->connectToExit(node->getItem());
          }
        }
      }

      // Look for all instructions of variables which are read-only and declared in the function
      bool isWrite;
      for(auto node : DG->getNodes()){
        if(node != DG->getEntry() && node != DG->getExit()){
          isWrite = isa<StoreInst>(node->getItem());
          varName = node->getItem()->getOperand(isWrite ? 1 : 0)->getName().str();
          if(unsafeOperands.find(node->getItem()->getOperand(isWrite ? 1 : 0)) != unsafeOperands.end()){
            declareMap[varName] = true;
          }
          if(!isSafe(node->getItem())/* || isWrite*/){
            declareMap[varName] = true;
          }
          ++instrCount;
        }
      }


      ofstream stream;
      stream.open("ignoring_intructions.txt", ios_base::app);
      if (!stream.is_open())
      {
        errs() << "Problem opening file: ignoring_intructions.txt\n";
        return false;
      }
      for(auto node : DG->getNodes()){
        if(node != DG->getEntry() && node != DG->getExit()){
          isWrite = isa<StoreInst>(node->getItem());
          varName = node->getItem()->getOperand(isWrite ? 1 : 0)->getName().str();
          if(declareMap.count(varName) > 0 && !declareMap[varName]/* || varName == "retval"*/){
            CFG->getNode(node->getItem())->highlight();
            node->highlight();
            DebugLoc dl = node->getItem()->getDebugLoc();
            stream
              << (isWrite ? "w" : "r")
              << "|" << node->getItem()->getOperand(isWrite ? 1 : 0)->getName().str()
              << "|" << dl.getLine()
              << "|" << dl.getCol()
              << "\n"
            ;
            ++iinstrCount;
          }
        }
      }
      // errs() << "Instructions found for " << F.getName() << " (2): " << c << "\n";
      // errs() << "possibleFPVs: [";
      // for(string s : possibleFPVs){
        // errs() << s << ", ";
      // }

      // errs() << "]\n";



      recursiveDepFinder();

      errs() << "\tPrinting CFG to " << F.getName().str() + "_cfg.dot\n";
      CFG->dumpToDot(F.getName().str() + "_cfg.dot");

      errs() << "\tPrinting DepGraph to " << F.getName().str() + "_deps.dot\n";
      DG->dumpToDot(F.getName().str() + "_deps.dot");
      DG->dumpInstructionInfo();
      /*
      // Remove possible false positives
      
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
            //  errs() << "Removing edge " << DG->getNodeIndex(src) << " -> " << DG->getNodeIndex(src) << "\n";
             DG->removeEdge(edge);
          }
        }
      }
      

      DG->dumpToDot(F.getName().str() + "_deps2.dot");
      */
      // errs() << "done2\n";
      return false;
    }

    bool isSafe(Instruction* I) {
      for(Type* subType : I->getOperand(isa<StoreInst>(I) ? 1 : 0)->getType()->subtypes()){
        if(!isSafe(subType))
          return false;
      }
      return true;
    }

    bool isSafe(Type* type){
      return !type->isPointerTy() && !type->isArrayTy();
    }

    void recursiveDepFinder(){
      errs() << "recursiveDepFinder\n";
      vector<Instruction*>* checkedInstructions = new vector<Instruction*>();
      for(auto edge: CFG->getInEdges(CFG->getExit())){
        recursiveDepFinderHelper1(checkedInstructions, edge->getSrc()->getItem());
      }
    }

    void recursiveDepFinderHelper1(vector<Instruction*>* checkedInstructions, Instruction* I){
      errs() << "Checking dependencies for " << CFG->getNodeIndex(I) << "\n";
      checkedInstructions->push_back(I);
      for(auto edge: CFG->getInEdges(I)){
        if(isa<StoreInst>(I) || isa<LoadInst>(I)){
          recursiveDepFinderHelper2(new vector<Instruction*>(), I, edge->getSrc()->getItem());
        }
        if(find(checkedInstructions->begin(), checkedInstructions->end(), edge->getSrc()->getItem()) == checkedInstructions->end()){
          recursiveDepFinderHelper1(checkedInstructions, edge->getSrc()->getItem());
        }else{
          errs() << "\tAlready checked " << CFG->getNodeIndex(edge->getSrc()->getItem()) << "\n";
        }
      }
    }

    void recursiveDepFinderHelper2(vector<Instruction*>* checkedInstructions, Instruction* I, Instruction* C){
      checkedInstructions->push_back(C);
      errs() << "\t" <<  CFG->getNodeIndex(C) <<": ";
      if(CFG->getNode(C) == CFG->getEntry()){
        errs() << "A\n";
        return;
      }
      string varNameSrc = I->getOperand(isa<StoreInst>(I) ? 1 : 0)->getName().str();
      if (DbgDeclareInst* DbgDeclare = dyn_cast<DbgDeclareInst>(C)) {
        if(DbgDeclare->getAddress()->getName().str() == varNameSrc){
          errs() << "B\n";
          return;
        }
      }else if (DbgValueInst* DbgValue = dyn_cast<DbgValueInst>(C)) {
        if(DbgValue->getValue()->getName().str() == varNameSrc){
          errs() << "B\n";
          return;
        }
      }

      if(varNameSrc != C->getOperand(isa<StoreInst>(C) ? 1 : 0)->getName().str()){
        errs() << "C\n";
        goto next;
      }
    
      if(auto D = DI->depends(C, I, true)){
        if (D->isOutput())
        {
            DG->addEdge(I, C, EdgeDepType::WAW);
            errs() << "WAW\n";
            return;
        }
        else if (D->isFlow())
        {
            DG->addEdge(I, C, EdgeDepType::RAW);
            errs() << "RAW\n";
            return;
        }
        else if (D->isAnti())
        {
            DG->addEdge(I, C, EdgeDepType::WAR);
            errs() << "WAR\n";
            return;
        }else{
          errs() << "RAR\n";
          goto next;
        }
        if(
          (LI->getLoopFor((*C).getParent()) || LI->getLoopFor((*I).getParent()))
            && (*C).getParent() != (*I).getParent()
        ){
          // errs() << " (boundary dep)" ;
        }
        // errs() << "\n";
      }
      next:;
      
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
