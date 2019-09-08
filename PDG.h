#ifndef PDG_H
#define PDG_H

//LLVM IMPORTS
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/DominanceFrontier.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/IntrinsicInst.h"

//STL IMPORTS
#include <string>
#include <limits.h> 
#include <map>
#include <set>
#include <queue>

//LOCAL IMPORTS
#include "Graph.hpp"
#include "EdgeDepType.h"

#define ENTRY 1000000
#define EXIT 2000000

using namespace llvm;
using namespace std;
using PDE = Edge<Instruction*, EdgeDepType>;
using PDN = Node<Instruction*>;

class PDG : public Graph<Instruction*, EdgeDepType>
{
private:
	std::string functionName;
	Function *F;
	Node<Instruction*> *entry;
	Node<Instruction*> *exit;
	std::set<Graph<Instruction*, EdgeDepType>* > scSubgraphs;

public:
	PDG(std::string fName, Function *F)
		: functionName(fName)
		, F(F)
		, entry(nullptr)
		, exit(nullptr)
		{
			entry = addNode((Instruction*)ENTRY);
			exit = addNode((Instruction*)EXIT);
		}
	PDG()
		: functionName("NONE")
		, F(nullptr)
		, entry(nullptr)
		, exit(nullptr)
		{}
	~PDG()
	{
		delete entry;
		delete exit;
	}

	void dumpToDot(std::string graphName);
	void dumpToDot();
	std::string edgeLabel(Edge<Instruction*, EdgeDepType> *e);
	void connectToEntry(Instruction* inst);
	void connectToExit(Instruction* inst);
	Node<Instruction*> *getEntry() { return entry; }
	Node<Instruction*> *getExit() { return exit; }
	std::set<Graph<Instruction*, EdgeDepType>* > getStronglyConnectedSubgraphs();
	map<string, set<string>> getDPDepMap();
	
private:
	bool isTransitive(PDE* edge);
	bool hasPathTo(PDN* src, PDN* dst);
	map<PDN*, map<PDN*, int>> distanceMap;
	void setShortestDistances();
};

#endif // PDG_H
