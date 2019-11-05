#ifndef GRAPH_HPP
#define GRAPH_HPP
// #define DEBUG_GRAPH_HPP

//STL IMPORTS
#include <map>
#include <vector>
#include <set>
#include <stack>
#include <list>
#include <iostream>
#include <utility>
#include <algorithm>
#include <iterator>

#include "llvm/Support/raw_ostream.h"

template<typename NodeT>
class Node
{
private:
	NodeT item;
	bool highlighted;
	std::string label;
public:
	Node(NodeT _item) 
		: item(_item)
		{highlighted = false;}
	~Node() {};
	void highlight(){
		highlighted = true;
	}
	bool isHighlighted(){
		return highlighted;
	}
	NodeT getItem() const { return item; }

};

template<typename NodeT, typename EdgeT>
class Edge
{
private:
	Node<NodeT> *src;
	Node<NodeT> *dst;
	EdgeT type;

public:
	Edge(Node<NodeT> *_src, Node<NodeT> *_dst, EdgeT _type, std::string _label, bool _direction)
		: src(_src)
		, dst(_dst)
		, type(_type)
		{}
	Edge(Node<NodeT> *_src, Node<NodeT> *_dst, EdgeT _type)
		: src(_src)
		, dst(_dst)
		, type(_type)
		{}
	~Edge() {};

	Node<NodeT> *getSrc() const { return src; }
	Node<NodeT> *getDst() const { return dst; }
	EdgeT getType() const { return type; }
	EdgeT operator+(Edge<NodeT, EdgeT> &other)
	{
		return this->type + other.type;
	}
};

using namespace std;
template<typename NodeT, typename EdgeT>
class Graph
{
private:
	unsigned nextIntKey = 0;
	//This stores a map from object of type T to it's respective pair (Key, Node)
	std::map<NodeT, std::pair<int, Node<NodeT>* > > nodes;
	std::list<Node<NodeT>* > nodesList;
	std::list<Edge<NodeT, EdgeT>* > edgesList;
	//This map stores all the outcoming edges from node of type T
	std::map<Node<NodeT>*, std::set<Edge<NodeT, EdgeT>*> > outEdges;
	//This map stores all the incoming edges to node of type T
	std::map<Node<NodeT>*, std::set<Edge<NodeT, EdgeT>*> > inEdges;

	void DFSUtil(NodeT n, NodeT search, vector<NodeT> currentPath, set<vector<NodeT>> &paths) 
	{
		currentPath.push_back(n);
		
		if(n == search){
			paths.insert(currentPath);
			return;
		}

		for (Edge<NodeT, EdgeT> *e : getOutEdges(n)){
			NodeT dst = e->getDst()->getItem();
			if(find(currentPath.begin(), currentPath.end(), dst) == currentPath.end()){
				DFSUtil(dst, search, currentPath, paths);
			}
		}
	}

public:
	Graph() {};
	~Graph()
	{
		for (auto &n : nodesList) delete n;
		for (auto &e : edgesList) delete e;
	}

	Node<NodeT> *operator[](NodeT item) const { return getNode(item); }

	Node<NodeT> *addNode(NodeT item)
	{
		if (nodes.count(item) == 0)
		{
			Node<NodeT> *node = new Node<NodeT>(item);
			nodes[item] = std::make_pair<int,  Node<NodeT>* >(nextIntKey, std::move(node));
			nodesList.push_back(node);
			nextIntKey++;
			return node;
		}
		else
		{
			#ifdef DEBUG_GRAPH_HPP
				std::cout << "\nTrying to add an already added item.\n";
			#endif
			return nodes.find(item)->second.second;
		}
	}

	Node<NodeT> *getNode(NodeT item)
	{
		if (nodes.count(item) == 0)
			return addNode(item);
		return nodes.find(item)->second.second;
	}

	Node<NodeT> *getNodeByIndex(const int index) const
	{
		for (const auto &pair_ : nodes)
		{
			if (pair_.second.first == index)
			{
				return pair_.second.second;
			}
		}
		return nullptr;	
	}

	int getNodeIndex(NodeT item) const
	{
		if (nodes.count(item) == 0)
			return -1;
		return nodes.find(item)->second.first;
	}

	int getNodeIndex(Node<NodeT> *node) const
	{
		for (auto &n : nodes)
		{
			if (n.second.second == node)
				return n.second.first;
		}
		return -1;
	}

	std::list< Node<NodeT>*> getNodes() const
	{
		return nodesList;
	}

	Edge<NodeT, EdgeT> *addEdge(Node<NodeT> *src, Node<NodeT> *dst, EdgeT e)
	{
		for(Edge<NodeT, EdgeT> *ed : outEdges[src]){
			if(ed->getDst() == dst && ed->getType() == e){
				return nullptr;
			}
		}
		Edge<NodeT, EdgeT> *edge = new Edge<NodeT, EdgeT>(src, dst, e);
		outEdges[src].insert(edge);
		inEdges[dst].insert(edge);
		edgesList.push_back(edge);
		return edge;
	}

	Edge<NodeT, EdgeT> *addEdge(NodeT src, NodeT dst, EdgeT e)
	{
		Node<NodeT> *src_ = getNode(src);
		Node<NodeT> *dst_ = getNode(dst);

		return addEdge(src_, dst_, e);
	}

	std::set<Edge<NodeT, EdgeT>*> getInEdges(Node<NodeT> *node) 
	{
		std::set<Edge<NodeT, EdgeT>*> inEdges_;
		if (inEdges.find(node) != inEdges.end())
			inEdges_ = inEdges[node];
		
		return inEdges_;
	}

	std::set<Edge<NodeT, EdgeT>*> getInEdges(NodeT item)
	{
		Node<NodeT> *node = getNode(item);
		
		return getInEdges(node);
	}

	std::set<Edge<NodeT, EdgeT>*> getOutEdges(Node<NodeT> *node) 
	{
		std::set<Edge<NodeT, EdgeT>*> outEdges_;
		if (outEdges.count(node) != 0)
			return outEdges[node];
		return outEdges_;
	}

	std::set<Edge<NodeT, EdgeT>*> getOutEdges(NodeT item)
	{	
		return getOutEdges(getNode(item));
	}

	void removeEdge(Edge<NodeT, EdgeT>* e)
	{
		auto out = e->getSrc();
		auto in = e->getDst();
		edgesList.remove(e);
		outEdges[out].erase(e);
		inEdges[in].erase(e);
	}

	std::list<Edge<NodeT, EdgeT>* > getEdges() const
	{
		return edgesList;
	}

	int size() const { return nextIntKey; }

	set<vector<NodeT>> getPaths(Node<NodeT>* start, Node<NodeT>* end){
		return getPaths(start->getItem(), end->getItem());
	}

	set<vector<NodeT>> getPaths(NodeT start, NodeT end){
		set<vector<NodeT>> paths;
		vector<NodeT> path;
		DFSUtil(start, end, path, paths);

		return paths;
	}
};

#endif // GRAPH_HPP
