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
#include "llvm/IR/Dominators.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "PDG.h"
#include "Graph.hpp"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/Analysis/CallGraph.h"

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
  string edgeLabel(Edge<Instruction*, EdgeDepType> *e)
{
	switch (e->getType())
	{
		case EdgeDepType::RAR: return "RAR";
		case EdgeDepType::RAWLC: return "RAW*";
		case EdgeDepType::WAW: return "WAW";
		case EdgeDepType::RAW: return "RAW";
		case EdgeDepType::WAR: return "WAR";
		case EdgeDepType::CTR: return "CTR";
		case EdgeDepType::PARENT: return "PARENT";
		case EdgeDepType::SCA:
		{
			if (e->getSrc()->getItem()->hasName())
				return e->getSrc()->getItem()->getName();
			else
				return "SCA";
		}
		default: return std::to_string(e->getType());
	}
}

  struct DepAnalysis : public FunctionPass {
    static char ID;
    DependenceInfo *DI;
    PDG *DG, *CFG;

    DepAnalysis() : FunctionPass(ID) {}

    void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
      
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.addRequired<PostDominatorTreeWrapperPass>();
      AU.addRequired<DependenceAnalysisWrapperPass>();
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.addRequired<CallGraphWrapperPass>();
      //AU.addRequired<RegionInfoPass>();
    }

    bool runOnFunction(Function &F) {
      /*
      if(F.getName() != "fft_twiddle_gen1"){
        return false;
      }
      */
      errs() << "\n---------- Omission Analysis on " << F.getName() << " (" << (isRecursive(&F)) << ") ----------\n";

      DebugLoc dl;
      set<Instruction*> omittableInstructions;
      set<Value*> localValues, writtenValues;
      Value *v;
      // Get local and written values (variables)
      for (inst_iterator I = inst_begin(F), SrcE = inst_end(F); I != SrcE; ++I) {
        if (DbgDeclareInst* DbgDeclare = dyn_cast<DbgDeclareInst>(&*I)) {
          localValues.insert(DbgDeclare->getAddress());
        } else if (DbgValueInst* DbgValue = dyn_cast<DbgValueInst>(&*I)) {
          localValues.insert(DbgValue->getValue());
        }else if(isa<StoreInst>(&*I)){
          if(I->getDebugLoc()){ // if has debugLoc, it's normal write inst (param init otherwise)
            writtenValues.insert(I->getOperand(1));
          }
        }
      }
      // Remove values passed outside by reference from localValues
      for (inst_iterator I = inst_begin(F), SrcE = inst_end(F); I != SrcE; ++I) {
        if(CallInst* call_inst = dyn_cast<CallInst>(&*I)){
          for(uint i = 0; i < call_inst->getNumOperands() - 1; ++i){
            v = call_inst->getArgOperand(i);
            localValues.erase(v);
          }
        }
        if(ReturnInst* ret_inst = dyn_cast<ReturnInst>(&*I)){
          localValues.erase(ret_inst->getReturnValue());
        }
      }

      for (inst_iterator I = inst_begin(F), SrcE = inst_end(F); I != SrcE; ++I) {
        if(isa<StoreInst>(&*I) || isa<LoadInst>(&*I)){
          dl = I->getDebugLoc();
          v = I->getOperand(isa<StoreInst>(&*I) ? 1 : 0);
          if(
            !dl // this can be removed as DiscoPoP doesn't instrument them anyways
            || (
              localValues.find(v) != localValues.end()
              && writtenValues.find(v) == writtenValues.end()
            ) 
            //|| v->getName() == "retval"
          ) omittableInstructions.insert(&*I);
        }
      }
      


      errs() << "\tBuilding DepGraph\n";
      DI = &getAnalysis<DependenceAnalysisWrapperPass>().getDI();
      DominatorTree& DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
      PostDominatorTree& PDT = getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree();
      DG = new PDG(F.getName(), &F);
      CFG = new PDG(F.getName(), &F);

      // Create Store/Load-CFG
      {
        std::function<void(BasicBlock*,Instruction*)> add_first_successor_store_load_instructions;
        add_first_successor_store_load_instructions = [&](BasicBlock *BB, Instruction* previousInstruction)
        {
          bool hasSuccessors = false;
          for (BasicBlock *S : successors(BB)) {
            hasSuccessors = true;
            for (Instruction &I : *S){
              DebugLoc dl = I.getDebugLoc();
              if(!dl) continue;
              if(isa<StoreInst>(I) || isa<LoadInst>(I)){
                CFG->addEdge(previousInstruction, &I, EdgeDepType::CTR);
                goto next;
              }else if(isa<DbgDeclareInst>(&I)){
                CFG->addEdge(previousInstruction, &I, EdgeDepType::CTR);
                goto next;
              }
            }
            if(S != BB) 
              add_first_successor_store_load_instructions(S, previousInstruction);
            next:;
          }
          if(BB->getName().find("for.end") != string::npos && !hasSuccessors){
            CFG->connectToExit(previousInstruction);
          }
        };
        Instruction *previousInstruction;
        for (BasicBlock &BB : F){
          // Add current block's store/load-instructions and declarations to graph
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
            }else if(CFG->getOutEdges(node).empty()){
              CFG->connectToExit(node->getItem());
            }
          }
        }
      }

      recursiveDepFinder();
      Instruction *I, *J;
      set<string> tmpDeps, conditionalDeps;
      map<BasicBlock*, set<string>> conditionalDepMap;
      for(auto node : DG->getNodes()){
        if(node != DG->getEntry() && node != DG->getExit()){
          I = node->getItem();
          bool dom = true;
          tmpDeps.clear();
          for(auto edge: DG->getOutEdges(node)){
            J = edge->getDst()->getItem();
            if(I->getParent() == J->getParent()){
              for(auto &K: *I->getParent()){
                if(&K == I) goto next;
                if(&K == J) break;
              }
            }
            if(!PDT.dominates(I->getParent(), J->getParent())) goto next;
            tmpDeps.insert(
              to_string(I->getDebugLoc().getLine())
              + " NOM  " 
              + edgeLabel(edge) + " "
              + to_string(J->getDebugLoc().getLine()) + "|"
              + getVarName(I)
            );
          }
          for(auto edge: DG->getInEdges(node)){
            J = edge->getSrc()->getItem();
            if(I->getParent() == J->getParent()){  
              for(auto &K: *I->getParent()){
                if(&K == J) goto next;
                if(&K == I) break;
              }
            }
            if(!PDT.dominates(J->getParent(), I->getParent())) goto next;
            tmpDeps.insert(
              to_string(J->getDebugLoc().getLine())
              + " NOM  " 
              + edgeLabel(edge) + " "
              + to_string(I->getDebugLoc().getLine()) + "|"
              + getVarName(I)
            );
          }
          if(!dom) continue;
          v = I->getOperand(isa<StoreInst>(&*I) ? 1 : 0);
          if(localValues.find(v) != localValues.end()){
            omittableInstructions.insert(I);
            conditionalDepMap[I->getParent()].insert(tmpDeps.begin(), tmpDeps.end());
          }
          next:;
        }
      }
      
      errs() << "Load/Store Instructions:\n";
      iinstrCount += omittableInstructions.size();
      for (inst_iterator I = inst_begin(F), SrcE = inst_end(F); I != SrcE; ++I) {
        if(isa<StoreInst>(&*I) || isa<LoadInst>(&*I)){
          ++instrCount;
          errs() << "\t" << (isa<StoreInst>(&*I) ? "Write " : "Read ") << getVarName(&*I) << " | ";
          if(dl = I->getDebugLoc()) errs() << dl.getLine() << "," << dl.getCol();
          else errs() << "INIT";
          if(omittableInstructions.find(&*I) != omittableInstructions.end()){
            CFG->getNode(&*I)->highlight();
            DG->getNode(&*I)->highlight();
            errs() << " | (OMIT)";
          }
          errs() << "\n";
        }
      }

      errs() << "Conditional Dependences:\n";
      for(auto pair : conditionalDepMap){
        errs() << pair.first->getName() << ":\n";
        for(auto s: pair.second){
          errs() << "\t" << s << "\n";
        }
      }

      errs() << "Printing CFG to " << F.getName().str() + "_cfg.dot\n";
      CFG->dumpToDot(F.getName().str() + "_cfg.dot");

      errs() << "Printing DepGraph to " << F.getName().str() + "_deps.dot\n";
      DG->dumpToDot(F.getName().str() + "_deps.dot");
      DG->dumpInstructionInfo();

      return false;
    }

    void recursiveDepFinder(){
      // errs() << "recursiveDepFinder\n";
      vector<Instruction*>* checkedInstructions = new vector<Instruction*>();
      for(auto edge: CFG->getInEdges(CFG->getExit())){
        recursiveDepFinderHelper1(checkedInstructions, edge->getSrc()->getItem());
      }
    }

    void recursiveDepFinderHelper1(vector<Instruction*>* checkedInstructions, Instruction* I){
      // errs() << "Checking dependencies for " << CFG->getNodeIndex(I) << "\n";
      checkedInstructions->push_back(I);
      for(auto edge: CFG->getInEdges(I)){
        if(isa<StoreInst>(I) || isa<LoadInst>(I)){
          recursiveDepFinderHelper2(new vector<Instruction*>(), I, edge->getSrc()->getItem());
        }
        if(find(checkedInstructions->begin(), checkedInstructions->end(), edge->getSrc()->getItem()) == checkedInstructions->end()){
          recursiveDepFinderHelper1(checkedInstructions, edge->getSrc()->getItem());
        }else{
          ;// errs() << "\tAlready checked " << CFG->getNodeIndex(edge->getSrc()->getItem()) << "\n";
        }
      }
    }

    void recursiveDepFinderHelper2(vector<Instruction*>* checkedInstructions, Instruction* I, Instruction* C){
      checkedInstructions->push_back(C);
      // errs() << "\t" <<  CFG->getNodeIndex(C) <<": ";
      if(CFG->getNode(C) == CFG->getEntry()){
        return;
      }
      if (DbgDeclareInst* DbgDeclare = dyn_cast<DbgDeclareInst>(C)) {
        if(DbgDeclare->getAddress() == I->getOperand(isa<StoreInst>(I) ? 1 : 0)){
          return;
        }
      }else if (DbgValueInst* DbgValue = dyn_cast<DbgValueInst>(C)) {
        if(DbgValue->getValue() == I->getOperand(isa<StoreInst>(I) ? 1 : 0)){
          return;
        }
      }
      
      /*
      if(I->getOperand(isa<StoreInst>(I) ? 1 : 0) != C->getOperand(isa<StoreInst>(C) ? 1 : 0)){
        goto next;
      }
      */
    
      if(auto D = DI->depends(C, I, true)){
        if (D->isOutput())
        {
            DG->addEdge(I, C, EdgeDepType::WAW);
            // errs() << "WAW\n";
            return;
        }
        else if (D->isFlow())
        {
            DG->addEdge(I, C, EdgeDepType::RAW);
            // errs() << "RAW\n";
            return;
        }
        else if (D->isAnti())
        {
            DG->addEdge(I, C, EdgeDepType::WAR);
            // errs() << "WAR\n";
            return;
        }else{
          // errs() << "RAR\n";
          goto next;
        }
      }
      next:;
      
      for(auto edge: CFG->getInEdges(C)){
        if(find(checkedInstructions->begin(), checkedInstructions->end(), edge->getSrc()->getItem()) == checkedInstructions->end()){
          recursiveDepFinderHelper2(checkedInstructions, I, edge->getSrc()->getItem());
        }
      }
    }

    bool isRecursive(Function* F){
      CallGraph *CG = &getAnalysis<CallGraphWrapperPass>().getCallGraph();
      const CallGraphNode *root = (*CG)[F];
      return isRecursiveHelper(root, F, CG, new set<Function*>());
    }

    bool isRecursiveHelper(const CallGraphNode* n, Function* F, const CallGraph *CG, set<Function*> *checkedFunctions){
      checkedFunctions->insert(n->getFunction());
      for(auto cgn : *n){
        if(cgn.second->getFunction() == F){
          return true;
        }
        if(checkedFunctions->find(cgn.second->getFunction()) == checkedFunctions->end())
          return isRecursiveHelper(cgn.second, F, CG, checkedFunctions);
      }
      return false;
    }

    string getVarName(Instruction *I){
      // errs() << "\tgetVarName: " << *I << "\n";

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
        string r = getVarName((Instruction*)I->getOperand(0));
        for(uint i = 1; i < I->getNumOperands(); ++i){
          if(isa<Instruction>(I->getOperand(i))){
            r += "[" + getVarName((Instruction*)I->getOperand(i)) + "]";
          }
        }
        return r;
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
      
      Value *v = (Value*)I;
      if(v->hasName()){
        return v->getName().str();
      }
      return "n/a";
    }
  };
}

char DepAnalysis::ID = 0;

static RegisterPass<DepAnalysis> X("dep-analysis", "Run the DepAnalysis algorithm. Generates a dependence graph", false, false);
//static cl::opt<bool, false> printToDot("printToDot", cl::desc("Print dot file containing the depgraph"), cl::NotHidden);
