#ifndef __NET_SHARED_
#define __NET_SHARED_

#include <queue>
#include <bitset>
#include <vector>
#include <set>
#include "utility.h"

using namespace std;
// handle
#define MAX_DIST 999999999999999.0
#define MAX_KEYWORDS 64

extern int NodeNum;
extern int EdgeNum;
extern int NNnum;

struct poiPair {
	int pid;
	int vi;
	int vj;
};

struct operation {
	bool isDelete;
	int pid;
	int vi;
	int vj;
	float dist;
	unsigned long long kwd;
};

struct vertexOperation{
	int nOfD;
	int nOfI;
	vector<operation> deleteV;
	vector<operation> insertV;
};

// *******修改 为了Operation操作测试*******************
struct updateTreeNode {
	bool isLeaf;
	
	int nOfDelete;
	int nOfInsert;
	int nOfRemain;
	int nOfOperation;
	int father;
	
	unsigned long long bitmap;
	vector<int> children;	
	map<int, vertexOperation> operations;
};

struct segmentTreeNode {
	bool isLeaf;
	int vStart;
	int vEnd;
	int pLeft;
	int pRight;
	int emptySize;
};

struct nOfEmpty {
	int vi;
	int sumEmpty;
};

// define the query point
struct roadParameter {
	int avgNKwd;
	int avgNPt;
};

struct QueryPoint
{
	int Ni, Nj;
	float dist_Ni;
	float distEdge;
};

struct Query {
	int k;
	unsigned long long keywords;
	vector<QueryPoint> querypts;
};

/*
ostream& operator<<(ostream& os, Query& Q)
{
	os << bitset<64>(Q.keywords).to_string() << " "<< Q.k;
	vector<QueryPoint> ::iterator iter = Q.querypts.begin();
	for (; iter != Q.querypts.end(); iter++) {
		os << "," << iter->Ni << " " << iter->Nj << " " << iter->dist_Ni;
	}
	return os;
}

struct POI
{
	int Ni, Nj;
	int pre;//Refine use only
	unsigned long long keywords;
	float dist_Ni;
	float dist_Nj;
	float dist_toquery;
};


struct POIComparison
{
	bool operator () (const POI& left, const POI& right) const
	{
		return left.dist_toquery> right.dist_toquery;
	}
};


ostream& operator<<(ostream& os, const POI& poi)
{
	os << "(" << poi.Ni << "," << poi.Nj << ") ";
	os << bitset<64>(poi.keywords).to_string();
	os << " distNi:" << poi.dist_Ni;
	os << " distQ:" << poi.dist_toquery;
	os << " preNode:" << poi.pre << endl;

	return os;
}
*/
struct DStepEvent
{
    double dist;
    int node;
};

struct DStepComparison
{
    bool operator () (const DStepEvent& left, const DStepEvent& right) const
    {
        return left.dist > right.dist;
    }
};

typedef	priority_queue<DStepEvent,vector<DStepEvent>,DStepComparison> DStepQueue;


struct point
{
    int Ni,Nj,pos;
};

//Modified by Qin Xu
//Denote POI on RoadEdge

// record the information of POIcc
struct InerNode
{
	int pid;
	float dis;
	unsigned long long vct;
};

struct edge
{
	int FirstRow;
	int Ni, Nj;
	float dist;
	unsigned long long sumkwds;
	FastArray<InerNode> pts;
	//float dLB,dUB;		// for gendata use only
};

typedef map<unsigned long long,edge*> EdgeMapType; // map node to edges

// build AdjList on fly
extern FastArray<int>* AdjList;
extern FastArray<point> PtList;
extern EdgeMapType EdgeMap;	// key: i0*NodeNum+j0

// get the key of edge
inline unsigned long long getKey(unsigned long long i, unsigned long long j)
{
	unsigned long long i0=i<j?i:j,j0=j<i?i:j;	// be careful of the order in other places
	//unsigned int key = (i0*NodeNum + j0);
	unsigned long long key = (i0*NodeNum + j0);
    return key; // map this edge to unique key
}
// break the index of key of edge
inline void breakKey(unsigned long long key,int& Ni,int& Nj)
{
    Ni=key/NodeNum;
    Nj=key%NodeNum;
}

//-------
// Step
//-------
struct StepEvent {
	float dist;
	int node, ClusID;	// ClusID for multiple expansion
	float accDist;		// posDist for gendata.cc only

	float gdist, hdist;
	float xc, yc;
	bool isSortAcc;
};

struct StepComparison
{
	bool operator () (const StepEvent& left, const StepEvent& right) const
	{
		return left.dist > right.dist;
	}
};

typedef	priority_queue<StepEvent, vector<StepEvent>, StepComparison> StepQueue;

//void printStepEvent(StepEvent& event);

/*
void printEdgeKeys()
{
    int Ni,Nj;
    printf("EdgeKeys:\n");
    EdgeMapType::iterator p=EdgeMap.begin();
    while (p!=EdgeMap.end())
    {
        edge* e=p->second;
        breakKey(p->first,Ni,Nj);
        printf("%d %d %d\n",Ni,Nj,(e==NULL));
        p++;
    }
}
*/
#endif // __NET_SHARED


