//LOCAL IMPORTS
#include "PDG.h"

//LLVM IMPORTS
#include "llvm/Support/raw_ostream.h"


//STL IMPORTS
#include <fstream>
#include <regex>

#define DEBUG_TYPE "dep-analysis"

static cl::opt<bool, false> removeTransitiveDeps("removeTransitiveDeps", cl::desc("Remove transitive dependencies"), cl::NotHidden);
static cl::opt<string> fmap("fmap", cl::desc("DP-FileMapping filename"), cl::value_desc("filename"));

string PDG::nodeLabel(Instruction *inst){
	std::function<std::string(Instruction*)> getVarName;
	getVarName = [&](Instruction* I)->std::string
	{
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
	};
	
	if(isa<StoreInst>(inst) || isa<LoadInst>(inst)){
		string ret = to_string(getNodeIndex(inst));
		ret += "\\n";
		if(isa<StoreInst>(inst)) ret += "write(";
		else ret += "read(";
		ret += getVarName(inst);
		ret += ") ";

		DebugLoc dl = inst->getDebugLoc();
		if(DebugLoc dl = inst->getDebugLoc()){
			ret += to_string(dl.getLine());
			ret += ", ";
			ret += to_string(dl.getCol());
		}
		return ret;
	}
	return "?";
}

string PDG::edgeLabel(Edge<Instruction*, EdgeDepType> *e)
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

void PDG::dumpToDot(){
	std::string graphName = functionName + ".dot";
	this->dumpToDot(graphName);
}

void PDG::dumpToDot(std::string graphName)
{
	
	// Write the graph to a DOT file
	ofstream dotStream;
	dotStream.open(graphName);
	if (!dotStream.is_open())
	{
		errs() << "Problem opening DOT file: " << graphName << "\n";
	}	
	else
	{
		dotStream << "digraph g {\n";

		// Create all nodes in DOT format
		for (auto node : getNodes())
		{
			if (node == this->entry)
				dotStream << "\t\"" << getNodeIndex(node) << "\" [label=entry];\n";
			else if (node == this->exit)
				dotStream << "\t\"" << getNodeIndex(node) << "\" [label=exit];\n";
			else if (node->getItem()){
				DebugLoc dl = node->getItem()->getDebugLoc();
				if(!dl) continue;
				Instruction *I = node->getItem();
				if(isa<StoreInst>(I) || isa<LoadInst>(I)){
					dotStream << "\t\"" << 
					getNodeIndex(node) 
					<< "\" [label=\"" << nodeLabel(node->getItem()) << "\"" 
					<< (node->isHighlighted() ? ",style=filled,fillcolor=red": "")
					<< "];\n";
				}else if(DbgDeclareInst* DbgDeclare = dyn_cast<DbgDeclareInst>(I)){
					dotStream << "\t\"" << 
					getNodeIndex(node) 
					<< "\" [label=\"" << getNodeIndex(node) << "\\n"
					<< "declare(" << DbgDeclare->getAddress()->getName().str() << "): "
					<<  (dl ? to_string(dl.getLine()) : "") << (dl ? "," : "") << (dl ? to_string(dl.getCol()) : "")
					<< "\"" << ",shape=rectangle,fillcolor=wheat,style=filled];\n";
				}
			}
		}

		dotStream << "\n\n";
		
		// Now print all outgoing edges and their labels
		for (auto e : getEdges())
		{	
			if(
				e->getType() == EdgeDepType::RAW
				|| e->getType() == EdgeDepType::WAR
				|| e->getType() == EdgeDepType::WAW 				
			){	
				std::string srcName = e->getSrc()->getItem()->getOperand(isa<StoreInst>(e->getSrc()->getItem()) ? 1 : 0)->getName().str();
				std::string dstName = e->getDst()->getItem()->getOperand(isa<StoreInst>(e->getDst()->getItem()) ? 1 : 0)->getName().str();
				if(srcName == dstName)
					dotStream << "\t\""
						<< getNodeIndex(e->getSrc()) 
						<< "\" -> \"" << getNodeIndex(e->getDst()) 
						<< "\" [label=\"" /*<< edgeLabel(e)*/ << "\"];\n"
					;	
			}else if(e->getType() == EdgeDepType::CTR){
				dotStream << "\t\"" 
					<< getNodeIndex(e->getSrc()) 
					<< "\" -> \"" << getNodeIndex(e->getDst()) 
					<< "\" [style=dotted];\n"
				;
			}else{
				dotStream << "\t\"" << getNodeIndex(e->getSrc()) << "\" -> \"" << getNodeIndex(e->getDst()) << "\" [label=\"" << edgeLabel(e) << "\"];\n";
			}
		}
		
		dotStream << "}";
		dotStream.close();
	}

	// errs() << "Finished generating dot file for " << functionName << "\n";
	// errs() << "\n\n";
}

void PDG::dumpInstructionInfo(){
	errs() << "dumpInstructionInfo()\n";
	ofstream stream;
	stream.open(functionName + "_intructions.txt");
	if (!stream.is_open())
	{
		errs() << "Problem opening DOT file: " << functionName << "_instructions.txt\n";
		return;
	}
	for (auto node : getNodes())
	{
		if(node != entry && node != exit && getInEdges(node).empty() && getOutEdges(node).empty()){
			DebugLoc dl = node->getItem()->getDebugLoc();
			if(dl && (isa<StoreInst>(*node->getItem()) || isa<LoadInst>(*node->getItem()))){
				bool isWrite = isa<StoreInst>(node->getItem());
				stream 
					<< (isWrite ? "w" : "r")
					<< "|" << node->getItem()->getOperand(isWrite ? 1 : 0)->getName().str()
					<< "|" << dl.getLine()
					<< "|" << dl.getCol()
					<< "\n"
				;
			}
		}
	}
	stream.close();
}

void PDG::connectToEntry(Instruction* inst)
{
	auto n = getNode(inst);
	addEdge(entry, n, EdgeDepType::CTR);
}

void PDG::connectToExit(Instruction* inst)
{
	auto n = getNode(inst);
	addEdge(n, exit, EdgeDepType::CTR);
}

map<string, set<string>> PDG::getDPDepMap(){
	map<string, string> filemap;
	if(fmap.length() > 0){
		ifstream inFileStream(fmap);
		if (!inFileStream.is_open())
		{
			errs() << "Problem opening FileMapping: " << fmap << "\n";
		}
		string line;
		string file, id;
		while (getline(inFileStream, line))
		{
			id = line.substr(0, line.find("\t"));
			file = line.substr(line.find("\t") + 1, line.length());
			filemap.insert(make_pair(file,id));
		}
		inFileStream.close();
	}
	
	map<string, set<string>> depMap;

	Instruction *SrcI, *DstI;
	DebugLoc srcDL, dstDL, dl;

	string varNameSrc, varNameDst, srcLine, dstLine, fileID;
    
	std::regex r (".+\\.[0-9]+");
	for(auto edge: getEdges()){
		if(edge->getType() != EdgeDepType::SCA && edge->getType() != EdgeDepType::RAR){
			SrcI = edge->getSrc()->getItem();
			DstI = edge->getDst()->getItem();

			srcDL = SrcI->getDebugLoc();
			dstDL = DstI->getDebugLoc();

			if(!srcDL || !dstDL){
				goto skip;
			}

            varNameSrc = SrcI->getOperand(isa<StoreInst>(&*SrcI) ? 1 : 0)->getName().str();
            varNameDst = DstI->getOperand(isa<StoreInst>(&*DstI) ? 1 : 0)->getName().str();
			
			if(varNameSrc != varNameDst){
				goto skip;
			}
			
			/*
			if(getNodeIndex(edge->getSrc()) <= getNodeIndex(edge->getDst())){
				// Deps when SRC is after DST in code should only happen in a loop
				Loop *LDst = LI->getLoopFor((&*DstI)->getParent());
				Loop *LSrc = LI->getLoopFor((&*SrcI)->getParent());	
				if(
					LSrc == nullptr || LDst == nullptr
					|| LSrc != LDst || declareMap[varNameSrc] != LSrc
				){
					goto skip;
				}
			}
			*/

			if (std::regex_match (varNameSrc, r)){
				std::size_t found = varNameSrc.find_last_of(".");
				varNameSrc.erase (varNameSrc.begin()+found, varNameSrc.end());
				varNameDst = varNameSrc;
			}

			auto *Scope = cast<DIScope>(dstDL.getScope());
			if(filemap.find(Scope->getFilename()) != filemap.end()){
				fileID = filemap[Scope->getFilename()];
			}else{
				fileID = "1";
			}
			
			dstLine = fileID + ":" + to_string(srcDL.getLine()); //+ "|" + varNameDst;// + "," + to_string(dstDL.getCol());
			srcLine = edgeLabel(edge) + " " + fileID + ":" + to_string(dstDL.getLine()) + "|" + varNameSrc;
										
			if (depMap.find(dstLine) == depMap.end()) {
				set<string> s;
				depMap[dstLine] = s;
			}
			depMap[dstLine].insert(srcLine);
		}
		skip:;
	}

	return depMap;
}



