#include <iostream>
#include <unordered_map>
#include <queue>
#include <bitset>
#include <algorithm>
#include "diskbased.h"
#include "egtree.h"
#include "netshare.h"
#include "gendata.h"
#include <fstream>
#include <sstream>
#include <math.h>
#include <stdio.h>
#include <unordered_set>
#include<io.h>
#include "netVornonoi.h"
//#pragma comment(lib,"ws2_32.lib")

using namespace std;

#define EGTD 1
#define EGETD 2
#define EGANN 3
#define TA 4
#define CE 5
#define NVD 6

#define INFINITE_MAX  INT64_MAX
#define MAX_KEYWORDN 64 

#define WFACTOR 1
// define the query path
//string basepath = "..\\aknndata\\tg";
string dataSetPath;
string basepath;

unsigned long long nOfPageAccessed;
//int nOfPageAccessed;
int nOfEdgeExpended;
unsigned long long nOfSEdgeExpended;

int algorithmId;
int nodeleft, noderight;
int BlkLen;
int i_capacity;
unsigned long long keyw;
unsigned long long interkeyw;

int NodeNum;
int poiNodeNum;
int EdgeNum;
int wholeloop;
FastArray<int>* AdjList;
FastArray<point> PtList;
EdgeMapType EdgeMap;	// key: i0*NodeNum+j0

FILE *PtFile, *AdjFile, *reAdjFile;
BTree *PtTree;
//map<int ,unsigned long long> iTedge;
//map<unsigned long long, int> edgenum;
//int poicnt = 0;
Query Q;

// for TKDE2005
#define min(a, b) (((a) < (b))? (a) : (b)  )
#define max(a, b) (((a) > (b))? (a) : (b)  )
#define ValAbs(x) (((x) >  0 )? (x) : -(x) )

//typedef map<int, float> DISTMAP;
typedef map<int, float> DISTMAP;
DISTMAP elem_map;
DISTMAP* DistMaps;	// only use cheap storage for range search
struct DistElem {
	int id;
	float dist;
};
typedef vector<DistElem> DistQueue;

BitStore* astar_Visits;		// tmp. bitmap for A* search

BitStore *raVisited, *saVisited; // top-k
int PrintLimit;

typedef vector<int> 	IntVec;
typedef vector<float> 	FloatVec;

FloatVec M_xcrd, M_ycrd, compdist, bestcompdist;

BitStore onSameEdge;
float** partdists;
//float bestdist;	// best value found so far

bool isNNquery = true;
bool isEuclidSpace = true;
bool isWeightUse = false;
char ptgrprtfn[255];
int NNnum;
bool isSumDist = false;
bool iscovertest = true;
DistQueue dQ_graph;
//extern BTree *PtTree;
//extern struct QueryPoint;
//extern QueryPoint* Q.querypts;
//extern int NodeNum;

//extern int Q.k;
//extern Query Q;

// end of TKDE2005
// *******Aggregate K Keyword Nearest Neighbor*************

int nOfAggregatePoint; //用于全局设置

int leafThre = 10;
//*************需要在开始的时候更新并在结束的时候更新******************
map<int, int> remainSpaceN; //保存每个叶子节点中剩余的空间（Delete-Insert+PreviousRemain）
map<int, int> remainSpaceV; //记录每个v,剩余空间

vector<nOfEmpty> sumSpace; //临时用于记录从开始，到当前v的剩余空间总和
vector<int> leafNid; //保存所有的叶子节点的ID
vector<segmentTreeNode> SegmentTree;

struct CInerNode
{
	bool operator () (const InerNode& left, const InerNode& right) const
	{
		return left.dis > right.dis;
	}
};

struct candidateAggPoint {
	int poid;
	float distance;
	int nodei;
	int nodej;
};

struct result {
	int nOfAggPoint;
	vector<candidateAggPoint> topK;
	float kthDist;
	unsigned long long inter;
	unsigned long long kwdnode;
	int sumpid;
	unsigned long time1;
	unsigned long time2;
};
result rs;

//*****************修改 为了Operation操作测试*****************

vector<updateTreeNode> UTree;


struct PartAddr {
	int part;
	int addr;
};

map<int, PartAddr> paID;
vector<TreeNode> EGT;
set<int> visitedNode; //record the  id of visitedNode treeNodeID

					  // for EGTD
struct edgeStatu {
	int vi;
	int isVisited; // hvisited = 0; visitedNode = 1;
	float sum;
	vector<float> qTbdist;
};
map<unsigned long long, edgeStatu> edgevisited; // edgeID, isVisited
vector<unsigned long long> queryedge;

// priority queue
struct pnode {
	bool isfilter;
	int nodeID;
	float dist;
	vector<vector<float>> bdist;
};


////////////////////////////////////VANN//////////////////
map<int, map<int, float>> reAdjListM; //重构后的路网的相邻链表
map<int, vcell> nvdM;
map<int, int> addressM;
map<unsigned long long, vector<edgePoi>> reEdgeMapM;


int findVCell(QueryPoint qp, int& num, edgeSegment& es) {
	int rtValue = -1;
	int ni = qp.Ni;
	int nj = qp.Nj;
	float distq = qp.dist_Ni;
	unsigned long long key = getKey(ni, nj);
	vector<edgePoi> vcid = reEdgeMapM[key]; //注意：这时候的vcid里面的poi是按照到Ni距离排好序的
	//map<int, float> ::iterator it = vcid.begin();
	float distsvid = 0, distevid = qp.distEdge;
	int svid = ni, evid = nj;
	for (int f = 0; f < vcid.size(); f++) {
		int id = vcid[f].pid;
		float distp = vcid[f].dist;
		if (distq > distp) {
			svid = id;
			distsvid = distp;
		}
		if (distq < distp) {
			evid = id;
			distevid = distp;
			break;
		}
		if (distp == distq) {
			cout << "恰好！" << endl;
			num = -1;
			rtValue = id;
			return rtValue;
		}
	}
	set<int> all;
	if ((svid < NodeNum) || (evid < NodeNum)) {
		if (svid < NodeNum) {
			if (reAdjListM.find(svid) == reAdjListM.end()) {			
				int add = addressM[svid];
				map<int, float> diskList = getreAdj(add);
				reAdjListM[svid] = diskList;
			}
			map<int, float> nbList = reAdjListM[svid];
			map<int, float> ::iterator itnb = nbList.begin();
			for (; itnb != nbList.end(); itnb++) {
				int id = itnb->first;
				if (id >= NodeNum) {
					if (all.find(id) == all.end()) all.insert(id);
				}
			}
		}
		else {
			if (all.find(svid) == all.end()) all.insert(svid);
		}
		if (evid < NodeNum) {
			if (reAdjListM.find(evid) == reAdjListM.end()) {
				int add = addressM[evid];
				map<int, float> diskList = getreAdj(add);
				reAdjListM[evid] = diskList;
			}
			map<int, float> nbList = reAdjListM[evid];
			map<int, float> ::iterator itnb = nbList.begin();
			for (; itnb != nbList.end(); itnb++) {
				int id = itnb->first;
				if (id >= NodeNum) {
					if (all.find(id) == all.end()) all.insert(id);
				}
			}
		}
		else {
			if (all.find(evid) == all.end()) all.insert(evid);
		}
	}
	else {
		all.insert(svid);
		all.insert(evid);
	}

	float qTos = distq - distsvid;
	float qToe = distevid - distq;
	int reNi, reNj;
	float pos;
	if (svid < evid) {
		reNi = svid;
		reNj = evid;
		pos = qTos;
		es.start = qTos;
		es.end = qToe;
	}
	else {
		reNi = evid;
		reNj = svid;
		pos = qToe;
		es.start = qToe;
		es.end = qTos;
	}
	es.ni = reNi;
	es.nj = reNj;
	es.border = pos;

	set<int> ::iterator ita = all.begin();
	for (; ita != all.end(); ita++) {
		int id = *ita;
		vector<edgeSegment> rg = nvdM[id].region;
		for (int j = 0; j < rg.size(); j++) {
			edgeSegment es = rg[j];
			int nit, njt;
			float start, end;
			nit = es.ni;
			njt = es.nj;
			start = es.start;
			end = es.end;
			if ((reNi == nit) && (reNj == njt) && (pos >= start) && (pos <= end)) {
				rtValue = id;
				// 注意：这里返回的是region中的位置不是border的位置
				num = j;
				break;
			}		
		}
		if (rtValue > 0) break;
	}
	return rtValue;
}

bool noCommon(vector<vector<int>>& candidate, vector<int>& common) {
	bool rtValue;
	vector<int> intersection;
	for (int i = 0; i < candidate.size(); i++) {
		if (0 == i) intersection = candidate[i];
		else {
			vector<int> temp = candidate[i];
			vector<int> result;
			

			for (int j= 0; j < intersection.size(); j++) {
				int id = intersection[j];
				if (find(temp.begin(),temp.end(),id) != temp.end()) result.push_back(id);
			}
			intersection.clear();
			intersection = result;
			// 这里有个问题，可能要先排序
			//set_intersection(intersection.begin(), intersection.end(), temp.begin(), temp.end(), intersection);
		}
	}
	common = intersection;
	if (intersection.size()<nOfAggregatePoint) rtValue = true;
	else rtValue = false;
	return rtValue;
}

struct qpair { // 用于记录每个查询点当前访问的最小距离
	int qid;
	float dist;
	bool isPOI;
};

struct tnTmin {
	int tnid;
	float tmin;
};

struct qpaircom
{
	bool operator () (const qpair& left, const qpair& right) const
	{
		return left.dist > right.dist;
	}
};
typedef priority_queue<qpair, vector<qpair>, qpaircom> tpQueryPQ;
tpQueryPQ queryPQ;


void findNext(unordered_set<int>& all, int qid, int& vcid, float& dist, map<int, map<int, vector<float>>>& an) {
	// 从当前qid包含的所有的近邻开始找下一个最近邻
	// bool isTrue = true;
	int lp = 0;
	while (true) {
		vcid = -1;
		dist = 0; 
		//cout << "findNext " << lp++ << " ";
		unordered_set<int>::iterator it = all.begin();
		for (; it != all.end(); it++) {
			int nid = *it;
			// 注意：这里neighbor和border里面的顺序应该是一样的，都是按照compare进行排序
			map<edgeSegment, vector<int>, Compare> temp = nvdM[nid].neighbor;
			map<edgeSegment, vector<int>, Compare>::iterator it2 = temp.begin();
			for (int lp=0; it2 != temp.end(); it2++,lp++) {
				edgeSegment ess = it2->first;				
				float ldist = an[qid][nid][lp];
				vector<int> nb = it2->second;
				for (int j = 0; j < nb.size(); j++) {
					int adjId = nb[j];
					if (all.find(adjId) != all.end()) continue;
					// 这里要格外注意？？？
					vector<float> distV2 = nvdM[adjId].borderTpoiborder[ess];
					float rdist = distV2[distV2.size() - 1];
					if (-1 == vcid) {
						vcid = adjId;
						dist = ldist + rdist;
					}
					else {
						if (ldist + rdist < dist) {
							vcid = adjId;
							dist = ldist + rdist;
						}
					}
				}
			}
		}
		// 修改an网络添加q到vcid边界的距离
		it = all.begin();
		for (; it != all.end(); it++) {
			int nid = *it;
			set<int> nbSet = nvdM[nid].neighborI;
			if (nbSet.find(vcid) == nbSet.end()) continue;
			// 注意：这里neighbor和border里面的顺序应该是一样的，都是按照compare进行排序
			map<edgeSegment, vector<float>, Compare> temp = nvdM[nid].borderTpoiborder;
			map<edgeSegment, vector<float>, Compare>::iterator it2 = temp.begin();
			for (int lp = 0; it2 != temp.end(); it2++, lp++) {
				edgeSegment ess = it2->first;
				float ldist = an[qid][nid][lp];
				if (nvdM[vcid].borderTpoiborder.find(ess) == nvdM[vcid].borderTpoiborder.end()) continue;
				map<edgeSegment, vector<float>, Compare>::iterator it3 = nvdM[vcid].borderTpoiborder.begin();
				int k; //记录ess在vcid中的位置
				for (k = 0; it3 != nvdM[vcid].borderTpoiborder.end(); it3++, k++) {
					edgeSegment esv = it3->first;
					if (isEqual(ess, esv)) {
						break;
					}
				}
				int bsize = nvdM[vcid].borderTpoiborder.size();
				if (k == bsize) cout << "k compute error!" << endl;
				bool isFirst = false;
				if (an[qid].find(vcid) == an[qid].end()) {// 直接赋值
					vector<float> qTdist(bsize);
					vector<float> bTb = nvdM[vcid].borderTpoiborder[ess];
					// 注意这里bsize=bTb.size()-1
					if (bsize != bTb.size() - 1) cout << "bSize compute error!" << endl;
					for (int t = 0; t < bsize; t++) {
						if (t != k) {
							float sdist = ldist + bTb[t];
							qTdist[t] = sdist;
						}
						else {
							qTdist[t] = ldist;
						}
					}
					an[qid][vcid] = qTdist;
				}
				else {
					vector<float> bTb = nvdM[vcid].borderTpoiborder[ess];	
					float sdist = 0;
					for (int t = 0; t < bsize; t++) {
						if (t != k) sdist = ldist + bTb[t];
						else sdist = ldist;
						if (an[qid][vcid][t]>sdist) an[qid][vcid][t] = sdist;
					}				
				}			
			}
		}

		all.insert(vcid);
		//cout << vcid << endl;
		if ((nvdM[vcid].kwd&Q.keywords) == Q.keywords) break;
	}
}

unordered_map<int, float> djkBorder(int start, float disstart, int end, float disend, vector<int> cands) {

	set<int> todo;
	todo.insert(cands.begin(), cands.end());

	unordered_map<int, float> result;
	set<int> visitedNode;
	unordered_map<int, float> q;

	q[start] = disstart;
	q[end] = disend;

	// start
	int minpos, adjnode;
	float min, weight;
	while (!todo.empty() && !q.empty()) {
		min = -1;
		for (unordered_map<int, float>::iterator it = q.begin(); it != q.end(); it++) {
			if (min < 0) {
				minpos = it->first;
				min = it->second;
			}
			else {
				if (it->second < min) {
					minpos = it->first;
					min = it->second;
				}
			}
		}

		// put min to result, add to visitedNode
		result[minpos] = min;
		visitedNode.insert(minpos);
		q.erase(minpos);

		if (todo.find(minpos) != todo.end()) {
			todo.erase(minpos);
		}
		if (reAdjListM.find(minpos) == reAdjListM.end()) {
			int add = addressM[minpos];
			map<int, float> diskList = getreAdj(add);
			reAdjListM[minpos] = diskList;
		}
		map<int, float> nb = reAdjListM[minpos];
		map<int, float> ::iterator itnb = nb.begin();

		for (; itnb != nb.end(); itnb++) {
			int nid = itnb->first;
			weight = itnb->second;
			//adjnode = graph[minpos].adjnodes[i];
			if (visitedNode.find(nid) != visitedNode.end()) continue;

			if (q.find(nid) != q.end()) {
				if (min + weight < q[nid]) {
					q[nid] = min + weight;
				}
			}
			else q[nid] = min + weight;
		}
	}

	// output
	unordered_map<int, float> output;
	for (int i = 0; i < cands.size(); i++) {
		output[cands[i]] = result[cands[i]];
	}

	// return
	return output;
}

void VANN() {

}

//void VANN() {
//	// 首先对于每个查询点，找到它对应的最近的VCell;
//	int qsize = Q.querypts.size();
//	vector<vector<int>> candidateAll(qsize, vector<int>());//保存每个查询点当前访问到的所有节点
//	vector<vector<int>> candidate(qsize, vector<int>());//保存每个查询点当前包含关键字的vid
//	
//	vector<float> NNDist(qsize,0); // 记录到所有查询点最近的距离
//	vector<float> FNNDist(qsize, 0); // 记录到所有查询点最近的距离
//	map<int, map<int, float>> qTcandidate; // 记录查询点到Candidate的距离
//	//map<int, map<unsigned long long, boolDist>> an; //记录查询点到borders的距离
//	map<int, map<int, vector<float>>> an;
//	an.clear();
//
//	for (int i = 0; i < qsize; i++) {
//		int num;
//		qpair qpa;
//		qpa.qid = i;
//		QueryPoint qp = Q.querypts[i];
//		if (an.find(i) == an.end()) {
//			map<int, vector<float>> mapan;
//			mapan.clear();
//			an[i] = mapan;
//		}
//		edgeSegment esq;
//		int vcellid = findVCell(qp, num, esq);
//		// 对于当前的vcellid，计算q到它的距离以及q到其border的距离
//		if (num < 0) {// 此时查询点的位置是VCellid
//			qpa.dist = 0;
//			if (an[i].find(vcellid) == an[i].end()) {
//				vector<float> temp;
//				temp.clear();
//				an[i][vcellid] = temp;
//			}
//			map<edgeSegment,vector<float>,Compare> borders = nvdM[vcellid].borderTpoiborder;
//			map<edgeSegment, vector<float>, Compare>::iterator itb = borders.begin();
//			for (int lp = 0; itb != borders.end(); itb++, lp++) {				
//				int psize = itb->second.size() - 1;
//				float dist = itb->second[psize];
//				an[i][vcellid].push_back(dist);
//			}
//		}
//		else {
//			if (an[i].find(vcellid) == an[i].end()) {
//				vector<float> temp;
//				temp.clear();
//				an[i][vcellid] = temp;
//			}
//			set<int> target;
//			vector<int> targetv;
//			// 初始将generator压入到这里
//			target.insert(vcellid);
//			targetv.push_back(vcellid);
//			map<edgeSegment, vector<float>, Compare> borders = nvdM[vcellid].borderTpoiborder;
//			map<edgeSegment, vector<float>, Compare>::iterator itb = borders.begin();
//			for (; itb != borders.end(); itb++) {
//				edgeSegment es = itb->first;
//				if (target.find(es.ni) == target.end()) {
//					target.insert(es.ni);
//					targetv.push_back(es.ni);
//				}
//				if (target.find(es.nj) == target.end()) {
//					target.insert(es.nj);
//					targetv.push_back(es.nj);
//				}
//			}
//			// 这是q到所有border的ni,nj的距离；
//			unordered_map<int, float> result = djkBorder(esq.ni, esq.start, esq.nj, esq.end, targetv);
//			qpa.dist = result[vcellid];
//			itb = borders.begin();
//			for (int lp = 0; itb != borders.end(); itb++, lp++) {
//				edgeSegment es = itb->first;
//				float disti, distj;
//				disti = result[es.ni] + es.border;
//				if (reAdjListM.find(es.ni) == reAdjListM.end()) {
//					int add = addressM[es.ni];
//					map<int, float> diskList = getreAdj(add);
//					reAdjListM[es.ni] = diskList;
//				}
//				distj = result[es.nj] + reAdjListM[es.ni][es.nj] - es.border;
//				if (disti < distj) distj = disti;
//				if ((es.ni == esq.ni) && (es.nj == esq.nj)) {
//					disti = fabs(es.border - esq.border);
//					if (disti < distj) distj = disti;
//				}
//				an[i][vcellid].push_back(distj);				
//			}
//		}
//
//		/*edgeSegment es = nvdM[vcellid].region[num];		
//		vector<float> nbdist = nvdM[vcellid].borderTpoiborder[es];
//		int size = nbdist.size() - 1;
//		float dist = nbdist[size];*/
//
//		candidateAll[i].insert(vcellid);		
//		if ((nvdM[vcellid].kwd & Q.keywords) == Q.keywords) {
//			candidate[i].insert(vcellid);
//			if (qTcandidate.find(i) == qTcandidate.end()) {
//				map<int, float> tp;
//				tp.clear();
//				tp[vcellid] = qpa.dist; 
//				qTcandidate[i] = tp;
//				NNDist[i] = qpa.dist;
//				FNNDist[i] = qpa.dist;
//			}
//			else {
//				qTcandidate[i][vcellid] = qpa.dist;
//				//NNDist[i] = qpa.dist;
//				FNNDist[i] = qpa.dist;
//			}
//		}
//		queryPQ.push(qpa);
//	}
//
//	// 不断扩展当前队列直到交集不为空；
//	float aggDist = 0;
//	int rtPOI = -1;
//	vector<int> common;
//	while (noCommon(candidate, common)) {
//		// 注意这里弹出来的是不是距离最小的？？？
//		qpair qpa = queryPQ.top();
//		queryPQ.pop();
//		int qid = qpa.qid;
//		int vcid;
//		float vdist;
//		findNext(candidateAll[qid], qid, vcid, vdist, an);
//		
//		qpa.dist = vdist;
//		queryPQ.push(qpa);
//
//		candidate[qid].insert(vcid);
//		if (qTcandidate.find(qid) == qTcandidate.end()) {
//			map<int, float> tp;
//			tp.clear();
//			tp[vcid] = vdist; 
//			qTcandidate[qid] = tp;
//			NNDist[qid] = vdist;
//			FNNDist[qid] = vdist;
//		}
//		else {
//			qTcandidate[qid][vcid] = vdist; 				
//			FNNDist[qid] = vdist;
//		}
//	}
//
//	// 当前已经有共同的了，那么就可以过滤Candidate中的元素了
//	//1:构建S集合
//	unordered_set<int> S;
//	//vector<unordered_set<int>>::iterator iac = candidate;
//	for (int k = 0; k < candidate.size(); k++) {
//		unordered_set<int> tpSet = candidate[k];
//		unordered_set<int>::iterator itS = tpSet.begin();
//		for (; itS != tpSet.end(); itS++) {
//			int tid = *itS;
//			if (S.find(tid) == S.end()) S.insert(tid);
//		}
//	}
//
//	//2:计算aggregatedist
//	unordered_set<int>::iterator itC = common.begin();
//	for (; itC != common.end(); itC++) {
//		int cid = *itC;
//		rtPOI = cid;
//		for (int k = 0; k < qsize; k++) {
//			if (isSumDist) aggDist += qTcandidate[k][cid];
//			else {
//				if (aggDist < qTcandidate[k][cid]) aggDist = qTcandidate[k][cid];
//			}
//		}
//	}
//
//	while (S.size()>nOfAggregatePoint) {
//		cout << "S.size() is : " << S.size() << endl;
//		qpair qpa = queryPQ.top();
//		queryPQ.pop();
//		int qid = qpa.qid;
//		int vcid;
//		float vdist;
//		findNext(candidateAll[qid], qid, vcid, vdist, an);
//		qpa.dist = vdist;
//		qpa.qid = qid;
//		queryPQ.push(qpa);
//
//		// 注意：这里是不是要把vcid加入Candidate中
//		candidate[qid].insert(vcid);
//		// 计算dist
//		float tdist = 0;
//		for (int k = 0; k < candidate.size(); k++) {
//			unordered_set<int> tpSet = candidate[k];
//			if (isSumDist) {
//				if (tpSet.find(vcid) == tpSet.end()) tdist = tdist + NNDist[k];
//				else tdist = tdist + qTcandidate[k][vcid];
//			}
//			else {
//				if (tpSet.find(vcid) == tpSet.end()) {
//					if (tdist < FNNDist[k]) tdist = FNNDist[k];
//				}
//				else {
//					if (tdist < qTcandidate[k][vcid]) tdist = qTcandidate[k][vcid];
//				}
//			}			
//		}
//		if (tdist > aggDist) {
//			unordered_set<int> SPlus;
//			for (int k = 0; k < candidate.size(); k++) {
//				unordered_set<int> tpSet = candidate[k];
//				if (tpSet.find(vcid) != tpSet.end()) {
//					unordered_set<int>::iterator its = tpSet.begin();
//					for (; its != tpSet.end(); its++) {
//						int id = *its;
//						if (id != vcid) {
//							if (SPlus.find(id) == SPlus.end()) SPlus.insert(id);
//						}
//						else break;
//					}					
//				}
//			}
//			// 过滤S
//			unordered_set<int>::iterator itS = S.begin();
//			unordered_set<int> tempS;
//			for (; itS != S.end(); itS++) {
//				int fid = *itS;
//				if (SPlus.find(fid) != SPlus.end()) tempS.insert(fid);
//			}
//			S.clear();
//			S = tempS;
//		}
//		else {
//			bool isVisitedByAll = true;
//			float adist = 0;
//			for (int k = 0; k < candidate.size(); k++) {
//				unordered_set<int> tpSet = candidate[k];
//				if (tpSet.find(vcid) == tpSet.end()) {
//					isVisitedByAll = false;
//					break;
//				}
//				else {
//					if (isSumDist) {
//						adist = adist + qTcandidate[k][vcid];
//					}
//					else {
//						if (adist < qTcandidate[k][vcid]) adist = qTcandidate[k][vcid];
//					}
//				}				
//			}
//			if (isVisitedByAll) {
//				if (adist < aggDist) {
//					aggDist = adist;
//					rtPOI = vcid;
//				}
//			}
//		}
//	}
//
//	cout << "VANN result is: " << rtPOI << " " << aggDist << endl;
//}


struct comparator
{
	bool operator () (const pnode& left, const pnode& right) const
	{
		return left.dist > right.dist;
	}
};
typedef	priority_queue<pnode, vector<pnode>, comparator> pnodePQ;
pnodePQ pq;

vector<map<int, vector<float>>> queryPath;

map<int,map<int, vector<float>>> vTNodeBorder; //map<nid,map<vid,vector<border>>>

struct pvertex {
	int vertexID;
	float sumDist;
	vector<float> vdist; // vertex-query points \ record the distance between Q to the border of this node
};

struct vcomparator
{
	bool operator () (const pvertex& left, const pvertex& right) const
	{
		return left.sumDist > right.sumDist;
	}
};
typedef	priority_queue<pvertex, vector<pvertex>, vcomparator> pvertexPQ;
// pnodePQ pq;

int getAdjListGrpAddr(int NodeID)  	// using AdjFile
{
	int address = 0;

	if (algorithmId < 4) {
		address = paID[NodeID].addr;
		//return paID[NodeID].addr;
	}
	else if (algorithmId < 6){
		int addr = sizeof(int) + NodeID*sizeof(int), GrpAddr;
		char* BlockAddr = getFlatBlock(AdjFile, addr / BlkLen);
		memcpy(Ref(GrpAddr), BlockAddr + (addr%BlkLen), sizeof(int));
		address = GrpAddr;
	}
	return address;
}

int partAddrLoad(const char* filename, map<int, PartAddr> &partID) {

	//printf("loading partAddrFile\n");
	//FILE *paFile;
	//paFile = fopen(filename, "r+");
	//CheckFile(paFile, filename);
	int nOfNode;
	//fread(&nOfNode, sizeof(int), 1, paFile);
	//int loop = 0;
	ifstream paFile(filename);
	string line;
	int loop = 0;
	while (!paFile.eof())
	{
		getline(paFile, line);
		//cout << loop++ << endl;
		if (line == "")
			continue;
		int nid, part, addr;
		istringstream iss(line);
		// --M-- read the unrelevant coordinates inf
		iss >> nid >> part >> addr;
		PartAddr pa;
		pa.addr = addr;
		pa.part = part;
		partID[nid] = pa;
		loop++;
		//printf("i:%d, nodeid:%d, part:%d, addr:%d\n", loop, nid, pa.part, pa.addr);
	}
	nOfNode = partID.size();
	paFile.close();
	return nOfNode;
}

int preprocessedge(string filename) {

	//printf("loading partAddrFile\n");
	//FILE *paFile;
	//paFile = fopen(filename, "r+");
	//CheckFile(paFile, filename);
	int nOfNode;
	//fread(&nOfNode, sizeof(int), 1, paFile);
	//int loop = 0;
	string iname = filename + "\\edge";
	string oname = filename + "\\road";
	ifstream iFile(iname);
	ofstream oFile(oname);
	string line;
	int loop = 0;
	while (!iFile.eof())
	{
		getline(iFile, line);
		//cout << loop++ << endl;
		if (line == "")
			continue;
		int eid, nid, njd;
		float dist;
		istringstream iss(line);
		// --M-- read the unrelevant coordinates inf
		iss >> eid >> nid >> njd >> dist;

		int dis = dist * 9;
		if (dis < 20) dis = dis + 20;
		oFile << eid << " " << nid << " " << njd << " " << dis << endl;
		//printf("i:%d, nodeid:%d, part:%d, addr:%d\n", loop, nid, pa.part, pa.addr);
	}

	iFile.close();
	oFile.close();
	return 0;
}

void comQueryPath(Query Q, vector<TreeNode> &EGT) {
	// compute the queryedge
	queryedge.clear();
	for (int t = 0; t < Q.k; t++) {
		unsigned long long ni, nj, key;
		QueryPoint q = Q.querypts[t];
		ni = q.Ni;
		nj = q.Nj;
		key = getKey(ni, nj);
		queryedge.push_back(key);
	}

	// 对于Q中的每个查询点，计算它的查询路径并保存到queryPath中
	vector<QueryPoint> ::iterator itr = Q.querypts.begin();
	for (; itr != Q.querypts.end(); itr++) {
		QueryPoint q = *itr;
		int pid = paID[q.Ni].part;
		// 计算叶子节点到查询点的距离
		int sizel = EGT[pid].leafnodes.size();
		float sum = 0.0;
		int posi = find(EGT[pid].leafnodes.begin(), EGT[pid].leafnodes.end(), q.Ni) - EGT[pid].leafnodes.begin();
		int posj = find(EGT[pid].leafnodes.begin(), EGT[pid].leafnodes.end(), q.Nj) - EGT[pid].leafnodes.begin();
		int pi = 0, pj = 0;
		int sizeb = EGT[pid].borders.size();
		vector<float> dis(sizeb, 0);
		map<int, vector<float>> nodePath;
		nodePath.clear();
		for (int j = 0; j < sizeb; j++) {
			pi = j*sizel + posi;
			pj = j*sizel + posj;
			float tempi = EGT[pid].mind[pi];
			float tempj = EGT[pid].mind[pj];
			tempi += q.dist_Ni;
			tempj += (q.distEdge - q.dist_Ni);
			if (tempi < tempj) {
				dis[j] = tempi;
			}
			else {
				dis[j] = tempj;
			}
		}
		nodePath[pid].assign(dis.begin(), dis.end());
		int preid;
		while (pid != 0) {
			//queryPath
			preid = pid;
			pid = EGT[pid].father;
			int sizep = EGT[pid].borders.size();
			vector<float> bdis(sizep, 0);
			for (int l = 0; l < sizep; l++) {
				int border = EGT[pid].borders[l];
				posi = find(EGT[pid].union_borders.begin(), EGT[pid].union_borders.end(), border) - EGT[pid].union_borders.begin();
				if (posi >(EGT[pid].union_borders.size() - 1)) cout << "error" << endl;
				float min = -1;
				for (int k = 0; k < EGT[preid].borders.size(); k++) {
					int preborder = EGT[preid].borders[k];
					int dist;
					posj = find(EGT[pid].union_borders.begin(), EGT[pid].union_borders.end(), preborder) - EGT[pid].union_borders.begin();
					int index;
					float predist = nodePath[preid][k];
					// be careful
					if (posi > posj) {
						index = ((posi + 1)*posi) / 2 + posj;
						dist = EGT[pid].mind[index];
						dist += predist;
					}
					else {
						index = ((posj + 1)*posj) / 2 + posi;
						dist = EGT[pid].mind[index];
						dist += predist;
					}
					if (min < 0) {
						min = dist;
					}
					else {
						if (dist < min) min = dist;
					}
				}
				bdis[l] = min;
			}
			nodePath[pid] = bdis;
		}

		queryPath.push_back(nodePath);
	}
	int f = 0;
}

void initialQuery(string fileprefix) {
	nOfPageAccessed = 0;
	nOfEdgeExpended = 0;
	nOfSEdgeExpended = 0;

	nodeleft = -1;
	noderight = -1;
	keyw = 0;
	interkeyw = 0;

	vector<candidateAggPoint> caggpoint;
	caggpoint.clear();
	rs.topK = caggpoint;
	rs.nOfAggPoint = nOfAggregatePoint;
	rs.kthDist = INFINITE_MAX;
	
	rs.sumpid = 0;
	rs.inter = 0;
	rs.kwdnode = 0;

	rs.time1 = 0;
	rs.time2 = 0;

	//paID.clear();
	EGT.clear();
	visitedNode.clear(); //record the  id of visitedNode treeNodeID
	edgevisited.clear(); // edgeID, isVisited
	while (!pq.empty()) pq.pop();
	queryPath.clear();
	paID.clear();
	reEdgeMapM.clear();
	addressM.clear();
	nvdM.clear();

	// 读取NodeNum和poiNodeNum
	ifstream iFile(fileprefix + "\\information");
	string line;
	while (!iFile.eof()) {
		getline(iFile, line);
		if (line == "") continue;
		istringstream iss(line);
		// --M-- read the unrelevant coordinates 
		iss >> NodeNum >> poiNodeNum;
		break;
	}
	iFile.close();

	if (algorithmId > 3) {
		if (algorithmId == 6) {
			//VANN
			reEdgeMapM = loadReEdgeMap(fileprefix);
			addressM = loadAddress(fileprefix);
			nvdM = loadNVD(fileprefix);
		}
		else {
			return;
		}
	}
	else {
		// load partaddr
		string name;
		name.clear();
		name = fileprefix + "\\partAddr";
		NodeNum = partAddrLoad(name.c_str(), paID);

		// load egtree
		name.clear();
		name = fileprefix + "\\egtree";
		//sprintf(tmpFileName, "%s\\egtree", fileprefix);
		// Note : 在这里初始化UTree
		egtree_load(name.c_str(), EGT, UTree);
		//comQueryPath(Q, EGT);
		leafNid.clear();
		for (int i = 0; i < EGT.size(); i++) {
			if (EGT[i].isleaf) leafNid.push_back(i);
		}
		remainSpaceN.clear();
		remainSpaceV.clear();
	}
}


//计算q到vertex的距离
vector<float> dijkstra_candidate(QueryPoint s, vector<int> &cands) {
	// init
	int AdjGrpAddr, AdjListSize, NewNodeID, PtGrpKey, PtNumOnEdge;
	float EdgeDist, PtDist;

	set<int> todo;
	todo.clear();
	todo.insert(cands.begin(), cands.end());

	unordered_map<int, float> result;
	result.clear();
	set<int> visitedNode;
	visitedNode.clear();
	unordered_map<int, float> q;
	q.clear();
	int vi = s.Ni;
	int vj = s.Nj;
	q[vi] = s.dist_Ni;
	q[vj] = s.distEdge - s.dist_Ni;

	// start
	int minpos, adjnode;
	float min;
	float weight;
	while (!todo.empty() && !q.empty()) {
		min = -1;
		for (unordered_map<int, float>::iterator it = q.begin(); it != q.end(); it++) {
			if (min < 0) {
				minpos = it->first;
				min = it->second;
			}
			else {
				if (it->second < min) {
					min = it->second;
					minpos = it->first;
				}
			}
			/*if (it->second < min) {
			min = it->second;
			minpos = it->first;
			}*/
		}

		// put min to result, add to visitedNode
		result[minpos] = min;
		visitedNode.insert(minpos);
		q.erase(minpos);

		if (todo.find(minpos) != todo.end()) {
			todo.erase(minpos);
		}

		// expand
		AdjGrpAddr = getAdjListGrpAddr(minpos);
		getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);

		for (int i = 0; i < AdjListSize; i++) {
			getVarE(ADJNODE_A, &adjnode, AdjGrpAddr, i);
			//adjnode = graph[minpos].adjnodes[i];
			if (visitedNode.find(adjnode) != visitedNode.end()) {
				continue;
			}

			nOfSEdgeExpended++;

			getVarE(DIST_A, &weight, AdjGrpAddr, i);
			int iedist = (int)weight;
			weight = iedist;
			//weight = graph[minpos].adjweight[i];

			if (q.find(adjnode) != q.end()) {
				if (min + weight < q[adjnode]) {
					q[adjnode] = min + weight;
				}
			}
			else {
				q[adjnode] = min + weight;
			}

		}
	}

	// output
	vector<float> output;
	for (int i = 0; i < cands.size(); i++) {
		output.push_back(result[cands[i]]);
	}

	// return
	return output;
}

float dijkstra(int nodei, int nodej, float upperbound) {
	// init
	int AdjGrpAddr, AdjListSize, NewNodeID, PtGrpKey, PtNumOnEdge;
	float EdgeDist, PtDist;
	set<int> todo;
	todo.clear();
	todo.insert(nodej);

	unordered_map<int, float> result;
	result.clear();
	set<int> visitedNode;
	visitedNode.clear();
	unordered_map<int, float> q;
	q.clear();
	int vi = nodei;
	//int vj = nodej;
	q[vi] = 0;
	//q[vj] = edgedist;

	// start
	int minpos, adjnode;
	float min;
	float weight;
	while (!todo.empty() && !q.empty()) {
		min = INFINITE_MAX;
		for (unordered_map<int, float>::iterator it = q.begin(); it != q.end(); it++) {
			/*if (min == -1) {
			minpos = it->first;
			min = it->second;
			}
			else {
			if (it->second < min) {
			min = it->second;
			minpos = it->first;
			}
			}*/
			if (it->second < min) {
				min = it->second;
				minpos = it->first;
			}
		}
		if (min > upperbound) break;
		// put min to result, add to visitedNode
		result[minpos] = min;
		visitedNode.insert(minpos);
		q.erase(minpos);

		if (todo.find(minpos) != todo.end()) {
			todo.erase(minpos);
		}

		// expand
		AdjGrpAddr = getAdjListGrpAddr(minpos);
		getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);

		for (int i = 0; i < AdjListSize; i++) {
			getVarE(ADJNODE_A, &adjnode, AdjGrpAddr, i);
			//adjnode = graph[minpos].adjnodes[i];
			if (visitedNode.find(adjnode) != visitedNode.end()) {
				continue;
			}
			nOfSEdgeExpended++;
			getVarE(DIST_A, &weight, AdjGrpAddr, i);
			//weight = graph[minpos].adjweight[i];

			if (q.find(adjnode) != q.end()) {
				if (min + weight < q[adjnode]) {
					q[adjnode] = min + weight;
				}
			}
			else {
				q[adjnode] = min + weight;
			}

		}
	}

	// output
	float dis = INFINITE_MAX;
	if (result.count(nodej) > 0) {
		dis = result[nodej];
	}

	// return
	return dis;
}

void EGTDA() {
	int AdjGrpAddr, AdjListSize, NewNodeID, PtGrpKey, PtNumOnEdge;
	unsigned long long sumkwd;
	float EdgeDist, PtDist;

	// step1 将根节点压入到优先队列中
	pnode pni;
	pni.dist = 0;
	pni.nodeID = 0;
	pq.push(pni);

	// step2 while循环，弹出当前最优的节点并展开
	while (!pq.empty()) {
		// step1 弹出top节点
		pnode node = pq.top();
		pq.pop();
		// if n没被过滤 Case1：叶子节点； Case2：中间节点
		int nid = node.nodeID;

		//printf("nodeid is:%d\n", nid);
		//if ((node.dist < rs.kthDist) && (EGT[nid].unionkwds&Q.keywords) == Q.keywords) {
		if ((node.dist < rs.kthDist)) {
			// Case1: 叶子节点
			if (EGT[nid].isleaf) {
				// 计算其中最优的点并更新rs.distance（内部和外部两种情况，内部用Dijkstra外部用边界距离）
				// 计算每个查询点到内部所有vertex的距离
				vector<pvertex> pv;
				pv.clear();
				for (int i = 0; i < Q.k; i++) {
					// 两种情况，case1：当前该查询点在该节点中，调用Dijkstra;case2:不在，直接相加
					//printf("The nid is:%d, q num is:%d\n", nid, i);
					map<int, vector<float>>::iterator it = queryPath[i].find(nid);
					vector<float> result;
					result.clear();
					if (it != queryPath[i].end()) { // 在里面，调用Dijkstra算法
													// note the corresponding relationship between result and leafnodes
						result = dijkstra_candidate(Q.querypts[i], EGT[nid].leafnodes);

						for (int l = 0; l < EGT[nid].leafnodes.size(); l++) {
							if (i == 0) {
								pvertex pt;
								vector<float> vf(Q.k, 0);
								pt.vdist = vf;

								pt.vertexID = EGT[nid].leafnodes[l];
								//pt.vdist.push_back(result[l]);
								pt.vdist[i] = result[l];
								pt.sumDist = result[l];
								pv.push_back(pt);
							}
							else {
								pv[l].vdist[i] = result[l];
								// ************modified*********
								if (isSumDist) {
									pv[l].sumDist += result[l];
								}
								else {
									if (result[l] > pv[l].sumDist) {
										pv[l].sumDist = result[l];
									}
								}
								//pv[l].sumDist += result[l];
							}
						}
					}

					else { // 直接相加
						int lnsize = EGT[nid].leafnodes.size();
						for (int l = 0; l < lnsize; l++) {
							if (i == 0) {
								pvertex pt;
								vector<float> vf(Q.k, 0);
								pt.vdist = vf;
								pt.vertexID = EGT[nid].leafnodes[l];

								int dist;
								float min = INFINITE_MAX;
								//int lnsize = EGT[nid].leafnodes.size();
								for (int m = 0; m < EGT[nid].borders.size(); m++) {
									int pos = m*lnsize + l;
									dist = EGT[nid].mind[pos] + node.bdist[m][i];
									if (dist < min) min = dist;
								}
								// 可能有问题，vdist未初始化
								pt.vdist[i] = min;
								pt.sumDist = min;
								pv.push_back(pt);
							}
							else {
								// 计算到q-border-vertex的距离
								int dist;
								float min = INFINITE_MAX;
								for (int m = 0; m < EGT[nid].borders.size(); m++) {
									int pos = m*lnsize + l;
									dist = EGT[nid].mind[pos] + node.bdist[m][i];
									if (dist < min) min = dist;
								}
								// 可能有问题，vdist未初始化
								pv[l].vdist[i] = min;
								if (isSumDist) {
									pv[l].sumDist += min;
								}
								else {
									if (pv[l].sumDist < min) {
										pv[l].sumDist = min;
									}
								}
								//pv[l].sumDist += min;
							}
						}
					}
				}

				// 进一步优化在这里************
				// 处理每一个vertex相邻的边，看上面是否有满足条件的POI 
				for (int t = 0; t < pv.size(); t++) {
					//printf("loop %d to num %d\n", t, pv.size());
					pvertex pt = pv[t];
					int vid = pt.vertexID;
					unsigned long long vide = vid;
					AdjGrpAddr = getAdjListGrpAddr(vid);
					getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);
					for (int n = 0; n < AdjListSize; n++) {

						getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, n);
						//nOfSEdgeExpended++;
						getVarE(DIST_A, Ref(EdgeDist), AdjGrpAddr, n);
						int iedist = (int)EdgeDist;
						EdgeDist = iedist;
						getVarE(SUMKWD_A, &sumkwd, AdjGrpAddr, n);
						unsigned long long NewNodeIDe = NewNodeID;
						unsigned long long edge = getKey(vide, NewNodeIDe);
						// bool isonedge;

						map<unsigned long long, edgeStatu>::iterator it = edgevisited.find(edge);
						edgeStatu es;
						if (it != edgevisited.end()) {
							if (edgevisited[edge].isVisited == 0) { //处理一下
								getVarE(PTKEY_A, Ref(PtGrpKey), AdjGrpAddr, n);
								if (PtGrpKey == -1) {
									//cout<<"No POI existed on Edge where Q located."<<endl;
								}
								else {
									nOfEdgeExpended++;
									//getVarE(DIST_A, Ref(EdgeDist), AdjGrpAddr, n);
									getFixedF(SIZE_P, Ref(PtNumOnEdge), PtGrpKey);
									//Notice the order POI visitedNode on edge
									unsigned long long pkwd;
									int pid;
									for (int t = 0; t < PtNumOnEdge; t++) {
										getVarE(PT_DIST, Ref(PtDist), PtGrpKey, t);
										int idist = (int)PtDist;
										PtDist = idist;
										getVarE(PT_KWD, &pkwd, PtGrpKey, t);
										getVarE(PT_P, &pid, PtGrpKey, t);
										if ((pkwd&Q.keywords) != Q.keywords) {
											continue;
										}
										else {
											edgeStatu es = it->second;
											float sum = 0;
											for (int f = 0; f < Q.k; f++) {

												float disi = 0;
												float disj = 0;

												if (vid < es.vi) {
													disi = PtDist + pt.vdist[f];
													disj = EdgeDist - PtDist + es.qTbdist[f];
												}
												else {
													disi = PtDist + es.qTbdist[f];
													disj = EdgeDist - PtDist + pt.vdist[f];
												}
												if (disi > disj) disi = disj;
												float sdis = INFINITE_MAX;
												if (queryedge[f] == edge) {
													sdis = fabsf(PtDist - Q.querypts[f].dist_Ni);
												}

												if (disi > sdis) disi = sdis;
												if (isSumDist) {
													sum = sum + disi;
												}
												else {
													if (sum < disi) sum = disi;
												}
												//sum = sum + disi;
											}
											// have computed the distance between each points to query:sum
											if (sum < rs.kthDist) {
												// 两种情况，如果已经有k个则更新，否则，直接加入
												if ((rs.topK.size()+1) <= rs.nOfAggPoint) {
													candidateAggPoint cap;
													cap.distance = sum;
													cap.poid = pid;
													cap.nodei = vid;
													cap.nodej = NewNodeID;
													rs.topK.push_back(cap);
												}
												else {
													// 找到最大的那个，判断是否需要更新
													//vector<candidateAggPoint> ::iterator itcap = rs.topK.begin();
													float maxdist = -1; int maxindex = -1;
													for (int lp = 0; lp < rs.topK.size(); lp++) {
														candidateAggPoint caplp = rs.topK[lp];
														if (maxdist < caplp.distance) {
															maxdist = caplp.distance;
															maxindex = lp;
														}
													}
													//rs.kthDist = maxdist;
													if (maxdist > sum) {
														rs.topK[maxindex].distance = sum;
														rs.topK[maxindex].poid = pid;
														rs.topK[maxindex].nodei = vid;
														rs.topK[maxindex].nodej = NewNodeID;
														//rs.kthDist = sum;
													}
													rs.kthDist = -1;
													for (int lp = 0; lp < rs.topK.size(); lp++) {
														candidateAggPoint caplp = rs.topK[lp];
														if (rs.kthDist < caplp.distance) {
															rs.kthDist = caplp.distance;
															//maxindex = lp;
														}
													}
													
												}																								
												rs.kwdnode = pkwd;
												rs.inter = (pkwd&Q.keywords);
											}
										}
									}
								}

								//edgevisited[edge].isVisited = 1;
							}
							// 两个顶点都访问过该条边了，可以删除了
							edgevisited.erase(it);
						}
						else { // 该条边未访问过
							nOfSEdgeExpended++;
							if ((sumkwd&Q.keywords) != Q.keywords) {
								es.isVisited = 1;
								edgevisited[edge] = es;
								//continue;
							}
							else {
								es.isVisited = 0;
								es.vi = vid;
								es.qTbdist.clear();
								es.qTbdist = pt.vdist;
								es.sum = pt.sumDist;
								edgevisited[edge] = es;
							}

						}
					}
				}

			}
			// Case2: 中间节点
			else {
				// 拓展该节点，并计算满足条件(关键字和距离)的孩子节点的距离并压入队列
				// 处理每一个孩子节点
				vector<pnode> childnode;
				childnode.clear();

				for (int i = 0; i < Q.k; i++) {
					// 按照查询路径来处理，处理每个查询点
					for (int j = 0; j < EGT[nid].children.size(); j++) {
						// two cases. 1: q in the node; 2: not in the node
						int cid = EGT[nid].children[j];

						if (i == 0) {
							pnode pn;
							pn.isfilter = true;
							pn.nodeID = cid;
							pn.dist = 0;
							for (int f = 0; f < EGT[cid].borders.size(); f++) {
								vector<float> vf(Q.k, 0);
								pn.bdist.push_back(vf);
							}
							childnode.push_back(pn);
						}
						if ((EGT[cid].unionkwds&Q.keywords) != Q.keywords) continue;
						childnode[j].isfilter = false;
						map<int, vector<float>>::iterator it = queryPath[i].find(cid);
						if (it != queryPath[i].end()) { // do nothing
							continue;
						}
						else { // compute the distance
							   // first determine the father node in the layer of cid
							int sid;
							bool flag = false;
							for (int l = 0; l < EGT[nid].children.size(); l++) {
								sid = EGT[nid].children[l];
								map<int, vector<float>>::iterator sit = queryPath[i].find(sid);
								if (sit != queryPath[i].end()) { // return this id
									flag = true;
									break;
								}
							}
							if (!flag) {
								sid = nid;
							}
							// then compute the distance from nid
							float mind = INFINITE_MAX;
							for (int k = 0; k < EGT[cid].borders.size(); k++) {
								// 计算每个查询点到所有border的距离
								int bdk = EGT[cid].borders[k];
								int posi = find(EGT[nid].union_borders.begin(), EGT[nid].union_borders.end(), bdk) - EGT[nid].union_borders.begin();
								float min = INFINITE_MAX;
								for (int t = 0; t < EGT[sid].borders.size(); t++) {
									int bdt = EGT[sid].borders[t];
									int posj = find(EGT[nid].union_borders.begin(), EGT[nid].union_borders.end(), bdt) - EGT[nid].union_borders.begin();
									// be careful
									int index;
									float dist;
									if (posi > posj) {
										index = ((posi + 1)*posi) / 2 + posj;
										dist = EGT[nid].mind[index];
									}
									else {
										index = ((posj + 1)*posj) / 2 + posi;
										dist = EGT[nid].mind[index];
									}
									if (flag) { // 
										map<int, vector<float>>::iterator nodeDist = queryPath[i].find(sid);
										dist = dist + nodeDist->second[t];
									}
									else {
										float distance = node.bdist[t][i];
										dist = dist + distance;
									}

									if (dist < min) min = dist;
								}
								if (min < mind) mind = min;
								// if is the first then initiate it
								childnode[j].bdist[k][i] = min;

							}
							// ***********modified
							if (isSumDist) {
								childnode[j].dist = childnode[j].dist + mind;
							}
							else {
								if (childnode[j].dist < mind) {
									childnode[j].dist = mind;
								}
							}
							//childnode[j].dist = childnode[j].dist + mind;
							//pq.push(pn);
						}
					}
				}
				int size = childnode.size();
				for (int loop = 0; loop < size; loop++) {
					if (childnode[loop].isfilter) continue;
					pq.push(childnode[loop]);
				}
			}
		}

	}

	// step3 处理half
	map<unsigned long long, edgeStatu> ::iterator it = edgevisited.begin();
	for (; it != edgevisited.end(); it++) {
		edgeStatu es = it->second;
		// 可能在边上
		unsigned long long edgeid = it->first;
		vector<unsigned long long> ::iterator itr = find(queryedge.begin(), queryedge.end(), edgeid);
		if ((itr == queryedge.end()) && (es.sum >= rs.kthDist)) continue;

		//unsigned long long vide, vjde;
		unsigned long long firste = it->first;
		int vid, vjd;
		breakKey(firste, vid, vjd);
		if (vid != es.vi) {
			int temp = vid;
			vid = vjd;
			vjd = temp;
		}
		// 可以优化在这里***********
		AdjGrpAddr = getAdjListGrpAddr(vid);
		getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);
		for (int n = 0; n < AdjListSize; n++) {
			getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, n);
			if (NewNodeID != vjd) continue;

			nOfSEdgeExpended++;
			getVarE(DIST_A, Ref(EdgeDist), AdjGrpAddr, n);
			int iedist = (int)EdgeDist;
			EdgeDist = iedist;
			//记录查询边距离
			getVarE(PTKEY_A, Ref(PtGrpKey), AdjGrpAddr, n);
			if (PtGrpKey == -1) {
				//cout<<"No POI existed on Edge where Q located."<<endl;
			}
			else {
				nOfEdgeExpended++;
				getFixedF(SIZE_P, Ref(PtNumOnEdge), PtGrpKey);
				//cout<<" PtNum on Edge where Q located:"<<PtNumOnEdge<<endl;
				//Notice the order POI visitedNode on edge
				unsigned long long pkwd;
				int pid;
				for (int j = 0; j < PtNumOnEdge; j++) {
					//poicnt++;
					getVarE(PT_DIST, Ref(PtDist), PtGrpKey, j);
					int ipdist = (int)PtDist;
					PtDist = ipdist;
					getVarE(PT_KWD, &pkwd, PtGrpKey, j);
					getVarE(PT_P, &pid, PtGrpKey, j);
					if ((pkwd&Q.keywords) != Q.keywords) {
						continue;
					}
					else {
						float sum = 0;

						for (int f = 0; f < Q.k; f++) {
							float dis;
							if (vid < vjd) {
								dis = PtDist;
								//sum = sum + Q.k*dis;
							}
							else {
								dis = EdgeDist - PtDist;
								//sum = sum + Q.k*dis;
							}
							// on the same edge
							float sdis = INFINITE_MAX;
							if (queryedge[f] == edgeid) {
								sdis = fabsf(PtDist - Q.querypts[f].dist_Ni);
							}
							if (dis > sdis) dis = sdis;

							if (isSumDist) {
								sum = sum + es.qTbdist[f] + dis;
							}
							else {
								if (sum < (es.qTbdist[f] + dis)) sum = es.qTbdist[f] + dis;
							}
							//sum = sum + es.qTbdist[f] + dis;								
						}
						
						if (sum < rs.kthDist) {
							// 两种情况，如果已经有k个则更新，否则，直接加入
							if ((rs.topK.size() + 1) <= rs.nOfAggPoint) {
								candidateAggPoint cap;
								cap.distance = sum;
								cap.poid = pid;
								cap.nodei = vid;
								cap.nodej = NewNodeID;
								rs.topK.push_back(cap);
							}
							else {
								// 找到最大的那个，判断是否需要更新
								//vector<candidateAggPoint> ::iterator itcap = rs.topK.begin();
								float maxdist = -1; int maxindex = -1;
								for (int lp = 0; lp < rs.topK.size(); lp++) {
									candidateAggPoint caplp = rs.topK[lp];
									if (maxdist < caplp.distance) {
										maxdist = caplp.distance;
										maxindex = lp;
									}
								}
								//rs.kthDist = maxdist;
								if (maxdist > sum) {
									rs.topK[maxindex].distance = sum;
									rs.topK[maxindex].poid = pid;
									rs.topK[maxindex].nodei = vid;
									rs.topK[maxindex].nodej = NewNodeID;
									//rs.kthDist = sum;
								}
								rs.kthDist = -1;
								for (int lp = 0; lp < rs.topK.size(); lp++) {
									candidateAggPoint caplp = rs.topK[lp];
									if (rs.kthDist < caplp.distance) {
										rs.kthDist = caplp.distance;
										//maxindex = lp;
									}
								}
							}
							rs.kwdnode = pkwd;
							rs.inter = (pkwd&Q.keywords);
						}

					}
				}
			}
		}


	}
	nOfPageAccessed = printPageAccess(-1);
	if (rs.topK.size() != rs.nOfAggPoint) cout << "Error in Top-k" << endl;
	int sumid = 0;
	for (int i = 0; i < rs.topK.size(); i++) {
		sumid = sumid + rs.topK[i].poid;
	}
	for (int l = 0; l < rs.topK.size(); l++) {
		cout << rs.topK[l].poid << " " << rs.topK[l].nodei << " " << rs.topK[l].nodej << " " << rs.topK[l].distance << endl;
	}
	rs.sumpid = sumid;
	//cout << rs.topK[0].nodei << " " << rs.topK[0].nodej << " " << rs.topK[0].distance << endl;
	//printf("The result of EGTDA distance is: %f\n", rs.kthDist);
	printf("The EGTDA sumid is: %d  \n", rs.sumpid);
	//printf("The result of TDA oid is: %d\n", rs.poid);
	//printf("The result of TDA pageaccessed is: %I64d\n", nOfPageAccessed);
	//printf("The result of TDA edgeexpand is: %d\n", nOfEdgeExpended);
	//printf("The result of TDA edgeSexpand is: %I64d\n", nOfSEdgeExpended); \
	//printf("The result of TDA nodei is: %d\n", rs.nodei);
	//printf("The result of TDA nodej is: %d\n", rs.nodej);
	//printf("The result of TDA distance is: %f\n", rs.distance);
	/*printf("The result of TDA oid is: %d\n", rs.poid);
	printf("The result of TDA edgeexpand is: %d\n", nOfEdgeExpended);
	printf("The result of TDA nodei is: %d\n", rs.nodei);
	printf("The result of TDA nodej is: %d\n", rs.nodej);*/
	//printf("The result of TDA kwdnode is: %llu\n", rs.kwdnode);
	//printf("The result of TDA interse is: %llu\n", rs.inter);
	//printf("The result of TDA querykwd is: %llu\n", Q.keywords);
}

bool iscontained(set<unsigned long long> coverkws, unsigned long long kwd) {
	set<unsigned long long> ::iterator it = coverkws.begin();
	bool iscontained = false;
	for (; it != coverkws.end(); it++) {
		unsigned long long key = *it;
		if ((key&kwd) == kwd) {
			iscontained = true;
			break;
		}
	}
	return iscontained;
}

void EGETDA() {

	int AdjGrpAddr, AdjListSize, NewNodeID, PtGrpKey, PtNumOnEdge;
	unsigned long long sumkwd;
	float EdgeDist, PtDist;
	//cout << paID[2943].part << " "<<paID[2965].part << endl;
	//return;
	// 初始化结果
	//rs.distance = INFINITE_MAX;
	//rs.poid = -1;
	edgevisited.clear();
	// step1 将根节点压入到优先队列中
	pnode pni;
	pni.dist = 0;
	pni.nodeID = 0;
	pq.push(pni);

	// step2 while循环，弹出当前最优的节点并展开
	while (!pq.empty()) {
		// step1 弹出top节点
		pnode node = pq.top();
		pq.pop();
		// if n没被过滤 Case1：叶子节点； Case2：中间节点
		int nid = node.nodeID;
		if (nid == 268 || nid == 77) {
			cout << nid << endl;
		}
		//printf("node is :%d\n", nid);
		//printf("nodeid is:%d\n", nid);
		if ((node.dist < rs.kthDist) && iscontained(EGT[nid].coverkwds, Q.keywords)) {
			// Case1: 叶子节点
			if (EGT[nid].isleaf) {
				// 计算其中最优的点并更新rs.distance（内部和外部两种情况，内部用Dijkstra外部用边界距离）
				// 计算每个查询点到内部所有vertex的距离
				vector<pvertex> pv;
				for (int i = 0; i < Q.k; i++) {
					// 两种情况，case1：当前该查询点在该节点中，调用Dijkstra;case2:不在，直接相加
					//printf("The nid is:%d, q num is:%d\n", nid, i);
					map<int, vector<float>>::iterator it = queryPath[i].find(nid);
					vector<float> result;
					if (it != queryPath[i].end()) { // 在里面，调用Dijkstra算法
													// note the corresponding relationship between result and leafnodes
						result = dijkstra_candidate(Q.querypts[i], EGT[nid].leafnodes);

						for (int l = 0; l < EGT[nid].leafnodes.size(); l++) {
							if (i == 0) {
								pvertex pt;
								vector<float> vf(Q.k, 0);
								pt.vdist = vf;

								pt.vertexID = EGT[nid].leafnodes[l];
								//pt.vdist.push_back(result[l]);
								pt.vdist[i] = result[l];
								pt.sumDist = result[l];
								pv.push_back(pt);
							}
							else {
								pv[l].vdist[i] = result[l];
								// ************modified*********
								if (isSumDist) {
									pv[l].sumDist += result[l];
								}
								else {
									if (result[l] > pv[l].sumDist) {
										pv[l].sumDist = result[l];
									}
								}
							}
						}
					}

					else { // 直接相加
						for (int l = 0; l < EGT[nid].leafnodes.size(); l++) {
							if (i == 0) {
								pvertex pt;
								vector<float> vf(Q.k, 0);
								pt.vdist = vf;
								pt.vertexID = EGT[nid].leafnodes[l];

								int dist;
								float min = INFINITE_MAX;
								for (int m = 0; m < EGT[nid].borders.size(); m++) {
									int pos = m*EGT[nid].leafnodes.size() + l;
									dist = EGT[nid].mind[pos] + node.bdist[m][i];
									if (dist < min) min = dist;
								}
								// 可能有问题，vdist未初始化
								pt.vdist[i] = min;
								pt.sumDist = min;
								pv.push_back(pt);
							}
							else {
								// 计算到q-border-vertex的距离
								int dist;
								float min = INFINITE_MAX;
								for (int m = 0; m < EGT[nid].borders.size(); m++) {
									int pos = m*EGT[nid].leafnodes.size() + l;
									dist = EGT[nid].mind[pos] + node.bdist[m][i];
									if (dist < min) min = dist;
								}
								// 可能有问题，vdist未初始化
								pv[l].vdist[i] = min;
								if (isSumDist) {
									pv[l].sumDist += min;
								}
								else {
									if (pv[l].sumDist < min) {
										pv[l].sumDist = min;
									}
								}
							}
						}
					}
				}

				// 进一步优化在这里************
				// 处理每一个vertex相邻的边，看上面是否有满足条件的POI 
				for (int t = 0; t < pv.size(); t++) {
					//printf("loop %d to num %d\n", t, pv.size());
					pvertex pt = pv[t];
					int vid = pt.vertexID;
					unsigned long long vide = vid;
					AdjGrpAddr = getAdjListGrpAddr(vid);

					getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);
					for (int n = 0; n < AdjListSize; n++) {
						getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, n);
						//nOfSEdgeExpended++;
						getVarE(DIST_A, Ref(EdgeDist), AdjGrpAddr, n);
						int iedist = (int)EdgeDist;
						EdgeDist = iedist;
						getVarE(SUMKWD_A, &sumkwd, AdjGrpAddr, n);
						if ((sumkwd&Q.keywords) != Q.keywords) continue;
						unsigned long long NewNodeIDe = NewNodeID;
						unsigned long long edge = getKey(vide, NewNodeIDe);
						// bool isonedge;

						map<unsigned long long, edgeStatu>::iterator it = edgevisited.find(edge);
						edgeStatu es;
						if (it != edgevisited.end()) {
							if (edgevisited[edge].isVisited == 0) { //处理一下
								getVarE(PTKEY_A, Ref(PtGrpKey), AdjGrpAddr, n);
								if (PtGrpKey == -1) {
									//cout << "No POI existed on Edge where Q located." << endl;
								}

								else {
									nOfEdgeExpended++;
									//getVarE(DIST_A, Ref(EdgeDist), AdjGrpAddr, n);
									//************ optimize in this part: 1.two vertex 2.kwds
									edgeStatu es = it->second;
									vector<unsigned long long> ::iterator itq = queryedge.begin();
									if ((itq == queryedge.end()) && ((es.sum >= rs.kthDist) && (pt.sumDist >= rs.kthDist))) continue;
									getFixedF(SIZE_P, Ref(PtNumOnEdge), PtGrpKey);
									//Notice the order POI visitedNode on edge
									unsigned long long pkwd;
									int pid;
									for (int t = 0; t < PtNumOnEdge; t++) {
										getVarE(PT_DIST, Ref(PtDist), PtGrpKey, t);
										int ipdist = (int)PtDist;
										PtDist = ipdist;
										getVarE(PT_KWD, &pkwd, PtGrpKey, t);
										getVarE(PT_P, &pid, PtGrpKey, t);

										if ((pkwd&Q.keywords) != Q.keywords) {
											continue;
										}
										else {
											edgeStatu es = it->second;
											float sum = 0;
											for (int f = 0; f < Q.k; f++) {

												float disi = 0;
												float disj = 0;

												if (vid < es.vi) {
													disi = PtDist + pt.vdist[f];
													disj = EdgeDist - PtDist + es.qTbdist[f];
												}
												else {
													disi = PtDist + es.qTbdist[f];
													disj = EdgeDist - PtDist + pt.vdist[f];
												}
												if (disi > disj) disi = disj;
												float sdis = INFINITE_MAX;
												if (queryedge[f] == edge) {
													sdis = fabsf(PtDist - Q.querypts[f].dist_Ni);
												}

												if (disi > sdis) disi = sdis;
												if (isSumDist) {
													sum = sum + disi;
												}
												else {
													if (sum < disi) sum = disi;
												}
												//sum = sum + disi;
											}
											// have computed the distance between each points to query:sum
											if (sum < rs.kthDist) {
												// 两种情况，如果已经有k个则更新，否则，直接加入
												if ((rs.topK.size() + 1) <= rs.nOfAggPoint) {
													candidateAggPoint cap;
													cap.distance = sum;
													cap.poid = pid;
													cap.nodei = vid;
													cap.nodej = NewNodeID;
													rs.topK.push_back(cap);
												}
												else {
													// 找到最大的那个，判断是否需要更新
													//vector<candidateAggPoint> ::iterator itcap = rs.topK.begin();
													float maxdist = -1; int maxindex = -1;
													for (int lp = 0; lp < rs.topK.size();  lp++) {
														candidateAggPoint caplp = rs.topK[lp];
														if (maxdist < caplp.distance) {
															maxdist = caplp.distance;
															maxindex = lp;
														}
													}
													//rs.kthDist = maxdist;
													if (maxdist > sum) {
														rs.topK[maxindex].distance = sum;
														rs.topK[maxindex].poid = pid;
														rs.topK[maxindex].nodei = vid;
														rs.topK[maxindex].nodej = NewNodeID;
														//rs.kthDist = sum;
													}
													rs.kthDist = -1;
													for (int lp = 0; lp < rs.topK.size();  lp++) {
														candidateAggPoint caplp = rs.topK[lp];
														if (rs.kthDist < caplp.distance) {
															rs.kthDist = caplp.distance;
															//maxindex = lp;
														}
													}

												}
												rs.kwdnode = pkwd;
												rs.inter = (pkwd&Q.keywords);
											}
										}
										
									}
								}

								//edgevisited[edge].isVisited = 1;
							}
							// 两个顶点都访问过该条边了，可以删除了
							edgevisited.erase(it);
						}
						else { // 该条边未访问过
							nOfSEdgeExpended++;
							if ((sumkwd&Q.keywords) != Q.keywords) {
								es.isVisited = 1;
								edgevisited[edge] = es;
								continue;
							}

							es.isVisited = 0;
							es.vi = vid;
							es.qTbdist = pt.vdist;
							es.sum = pt.sumDist;
							edgevisited[edge] = es;
						}
						//getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, n);
						//getVarE(DIST_A,Ref(EdgeDist),AdjGrpAddr,i);
					}

				}

			}
			// Case2: 中间节点
			else {
				// 拓展该节点，并计算满足条件(关键字和距离)的孩子节点的距离并压入队列
				// 处理每一个孩子节点
				vector<pnode> childnode;
				childnode.clear();

				for (int i = 0; i < Q.k; i++) {
					// 按照查询路径来处理，处理每个查询点
					for (int j = 0; j < EGT[nid].children.size(); j++) {
						// two cases. 1: q in the node; 2: not in the node

						int cid = EGT[nid].children[j];

						if (i == 0) {
							pnode pn;
							pn.isfilter = true;
							pn.nodeID = cid;
							pn.dist = 0;
							for (int f = 0; f < EGT[cid].borders.size(); f++) {
								vector<float> vf(Q.k, 0);
								pn.bdist.push_back(vf);
							}
							childnode.push_back(pn);
						}

						if ((EGT[cid].unionkwds&Q.keywords) != Q.keywords || !iscontained(EGT[cid].coverkwds, Q.keywords)) continue;
						childnode[j].isfilter = false;

						map<int, vector<float>>::iterator it = queryPath[i].find(cid);
						if (it != queryPath[i].end()) { // do nothing
							continue;
						}
						else { // compute the distance
							   // first determine the father node in the layer of cid
							int sid;
							bool flag = false;
							for (int l = 0; l < EGT[nid].children.size(); l++) {
								sid = EGT[nid].children[l];
								map<int, vector<float>>::iterator sit = queryPath[i].find(sid);
								if (sit != queryPath[i].end()) { // return this id
									flag = true;
									break;
								}
							}
							if (!flag) {
								sid = nid;
							}
							// then compute the distance from nid
							float mind = INFINITE_MAX;
							for (int k = 0; k < EGT[cid].borders.size(); k++) {
								// 计算每个查询点到所有border的距离
								int bdk = EGT[cid].borders[k];
								int posi = find(EGT[nid].union_borders.begin(), EGT[nid].union_borders.end(), bdk) - EGT[nid].union_borders.begin();
								float min = INFINITE_MAX;
								for (int t = 0; t < EGT[sid].borders.size(); t++) {
									int bdt = EGT[sid].borders[t];
									int posj = find(EGT[nid].union_borders.begin(), EGT[nid].union_borders.end(), bdt) - EGT[nid].union_borders.begin();
									// be careful
									int index;
									float dist;
									if (posi > posj) {
										index = ((posi + 1)*posi) / 2 + posj;
										dist = EGT[nid].mind[index];
									}
									else {
										index = ((posj + 1)*posj) / 2 + posi;
										dist = EGT[nid].mind[index];
									}
									if (flag) { // 
										map<int, vector<float>>::iterator nodeDist = queryPath[i].find(sid);
										dist = dist + nodeDist->second[t];
									}
									else {
										float distance = node.bdist[t][i];
										dist = dist + distance;
									}

									if (dist < min) min = dist;
								}
								if (min < mind) mind = min;
								// if is the first then initiate it
								childnode[j].bdist[k][i] = min;

							}
							//**********modified
							if (isSumDist) {
								childnode[j].dist = childnode[j].dist + mind;
							}
							else {
								if (childnode[j].dist < mind) childnode[j].dist = mind;
							}
							//childnode[j].dist = childnode[j].dist + mind;
							//pq.push(pn);
						}
					}
				}
				int size = childnode.size();
				for (int loop = 0; loop < size; loop++) {
					if (childnode[loop].isfilter) continue;
					pq.push(childnode[loop]);
				}
			}
		}

	}

	// step3 处理half
	map<unsigned long long, edgeStatu> ::iterator it = edgevisited.begin();
	for (; it != edgevisited.end(); it++) {
		edgeStatu es = it->second;
		// 可能在边上
		unsigned long long edgeid = it->first;
		vector<unsigned long long> ::iterator itr = find(queryedge.begin(), queryedge.end(), edgeid);
		if ((itr == queryedge.end()) && (es.sum >= rs.kthDist)) continue;

		//unsigned long long vide, vjde;
		unsigned long long firste = it->first;
		int vid, vjd;
		breakKey(firste, vid, vjd);
		if (vid != es.vi) {
			int temp = vid;
			vid = vjd;
			vjd = temp;
		}
		// 可以优化在这里***********
		AdjGrpAddr = getAdjListGrpAddr(vid);
		getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);
		for (int n = 0; n < AdjListSize; n++) {
			getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, n);
			if (NewNodeID != vjd) continue;
			nOfSEdgeExpended++;
			getVarE(DIST_A, Ref(EdgeDist), AdjGrpAddr, n);
			int iedist = (int)EdgeDist;
			EdgeDist = iedist;

			//记录查询边距离
			getVarE(PTKEY_A, Ref(PtGrpKey), AdjGrpAddr, n);
			if (PtGrpKey == -1) {
				//cout<<"No POI existed on Edge where Q located."<<endl;
			}
			else {
				nOfEdgeExpended++;
				getFixedF(SIZE_P, Ref(PtNumOnEdge), PtGrpKey);
				//cout<<" PtNum on Edge where Q located:"<<PtNumOnEdge<<endl;
				//Notice the order POI visitedNode on edge
				unsigned long long pkwd;
				int pid;
				for (int j = 0; j < PtNumOnEdge; j++) {
					//poicnt++;
					getVarE(PT_DIST, Ref(PtDist), PtGrpKey, j);
					int ipdist = (int)PtDist;
					PtDist = ipdist;
					getVarE(PT_KWD, &pkwd, PtGrpKey, j);
					getVarE(PT_P, &pid, PtGrpKey, j);
					if ((pkwd&Q.keywords) != Q.keywords) {
						continue;
					}
					else {
						float sum = 0;

						for (int f = 0; f < Q.k; f++) {
							float dis;
							if (vid < vjd) {
								dis = PtDist;
								//sum = sum + Q.k*dis;
							}
							else {
								dis = EdgeDist - PtDist;
								//sum = sum + Q.k*dis;
							}
							// on the same edge
							float sdis = INFINITE_MAX;
							if (queryedge[f] == edgeid) {
								sdis = fabsf(PtDist - Q.querypts[f].dist_Ni);
							}
							if (dis > sdis) dis = sdis;

							if (isSumDist) {
								sum = sum + es.qTbdist[f] + dis;
							}
							else {
								if (sum < (es.qTbdist[f] + dis)) sum = es.qTbdist[f] + dis;
							}
							//sum = sum + es.qTbdist[f] + dis;								
						}
						if (sum < rs.kthDist) {
							// 两种情况，如果已经有k个则更新，否则，直接加入
							if ((rs.topK.size() + 1) <= rs.nOfAggPoint) {
								candidateAggPoint cap;
								cap.distance = sum;
								cap.poid = pid;
								cap.nodei = vid;
								cap.nodej = NewNodeID;
								rs.topK.push_back(cap);
							}
							else {
								// 找到最大的那个，判断是否需要更新
								//vector<candidateAggPoint> ::iterator itcap = rs.topK.begin();
								float maxdist = -1; int maxindex = -1;
								for (int lp = 0; lp < rs.topK.size(); lp++) {
									candidateAggPoint caplp = rs.topK[lp];
									if (maxdist < caplp.distance) {
										maxdist = caplp.distance;
										maxindex = lp;
									}
								}
								//rs.kthDist = maxdist;
								if (maxdist > sum) {
									rs.topK[maxindex].distance = sum;
									rs.topK[maxindex].poid = pid;
									rs.topK[maxindex].nodei = vid;
									rs.topK[maxindex].nodej = NewNodeID;
									//rs.kthDist = sum;
								}
								rs.kthDist = -1;
								for (int lp = 0; lp < rs.topK.size(); lp++) {
									candidateAggPoint caplp = rs.topK[lp];
									if (rs.kthDist < caplp.distance) {
										rs.kthDist = caplp.distance;
										//maxindex = lp;
									}
								}

							}
							rs.kwdnode = pkwd;
							rs.inter = (pkwd&Q.keywords);
						}

					}
				}
			}
		}

	}
	nOfPageAccessed = printPageAccess(-1);
	if (rs.topK.size() != rs.nOfAggPoint) cout << "Error in Top-k" << endl;
	int sumid = 0;
	for (int i = 0; i < rs.topK.size(); i++) {
		sumid = sumid + rs.topK[i].poid;
	}
	rs.sumpid = sumid;
	//printf("The result of EGETDA distance is: %f\n", rs.kthDist);
	/*for (int l = 0; l < rs.topK.size(); l++) {
		cout << rs.topK[l].poid << " " << rs.topK[l].nodei << " " << rs.topK[l].nodej << " " << rs.topK[l].distance << endl;
	}*/

	printf("The EGETDA sumid is: %d\n", rs.sumpid);
	//printf("The result of ETDA oid is: %d\n", rs.poid);
	//printf("The result of ETDA pageaccessed is: %I64d\n", nOfPageAccessed);
	//printf("The result of ETDA edgeexpand is: %d\n", nOfEdgeExpended);
	//printf("The result of ETDA edgeSexpand is: %I64d\n", nOfSEdgeExpended);
	//printf("The result of ETDA nodei is: %d\n", rs.nodei);
	//printf("The result of ETDA nodej is: %d\n", rs.nodej);
	//printf("The result of ETDA distance is: %f\n", rs.distance);
	/*printf("The result of ETDA oid is: %d\n", rs.poid);
	printf("The result of ETDA edgeexpended is: %d\n", nOfEdgeExpended);
	printf("The result of ETDA nodei is: %d\n", rs.nodei);
	printf("The result of ETDA nodej is: %d\n", rs.nodej);*/
	//printf("The result of ETDA kwdnode is: %llu\n", rs.kwdnode);
	//printf("The result of ETDA interse is: %llu\n", rs.inter);
	//printf("The result of ETDA querykwd is: %llu\n", Q.keywords);
}



////////////////////////////////////////////////
float findInitial(QueryPoint qp, tpQueryPQ& tpq, int i, map<int, vector<float>>& mapan, tnTmin& tnm) {
	int AdjGrpAddr, AdjListSize, NewNodeID, PtGrpKey, PtNumOnEdge;
	unsigned long long sumkwd;
	float EdgeDist, PtDist;
	int qni = qp.Ni;
	int qnj = qp.Nj;
	int nid, posj;
	nid = paID[qni].part;
	tnm.tnid = nid;
	tnm.tmin = INFINITY;
	
	// 初始化，将nid中的所有结果加入到优先队列中便于后面访问
	if (mapan.find(nid) == mapan.end()) {
		vector<float> dist;
		dist.clear();
		mapan[nid] = dist;
	}

	vector<float> result = dijkstra_candidate(qp, EGT[nid].leafnodes);	
	for (int j = 0; j < EGT[nid].leafnodes.size(); j++) {
		int vid = EGT[nid].leafnodes[j];
		float ldist = result[j];
		// 注意这里要求border里面的顺序和leafnode里面顺序一样
		if (find(EGT[nid].borders.begin(), EGT[nid].borders.end(), vid) != EGT[nid].borders.end()) {
			mapan[nid].push_back(ldist);
			if (ldist < tnm.tmin) tnm.tmin = ldist;
		}
		//unsigned long long vide = vid;

		//if ((EGT[nid].unionkwds&Q.keywords) != Q.keywords) continue;

		AdjGrpAddr = getAdjListGrpAddr(vid);
		getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);
		for (int n = 0; n < AdjListSize; n++) {
			getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, n);
			getVarE(DIST_A, Ref(EdgeDist), AdjGrpAddr, n);
			int iedist = (int)EdgeDist;
			EdgeDist = iedist;
			getVarE(SUMKWD_A, &sumkwd, AdjGrpAddr, n);
			if ((sumkwd&Q.keywords) != Q.keywords) continue;
			//unsigned long long NewNodeIDe = NewNodeID;
			//unsigned long long edge = getKey(vide, NewNodeIDe);
			bool bothEdge = false;
			if (find(EGT[nid].leafnodes.begin(), EGT[nid].leafnodes.end(), NewNodeID) != EGT[nid].leafnodes.end()) {

				if (vid > NewNodeID) continue;
				bothEdge = true;
				for (int p = 0; p < EGT[nid].leafnodes.size(); p++) {
					if (EGT[nid].leafnodes[p] == NewNodeID) {
						posj = p;
						break;
					}
				}
			}
			getVarE(PTKEY_A, Ref(PtGrpKey), AdjGrpAddr, n);
			if (PtGrpKey == -1) {
				//cout<<"No POI existed on Edge where Q located."<<endl;
			}
			else {
				nOfEdgeExpended++;
				//getVarE(DIST_A, Ref(EdgeDist), AdjGrpAddr, n);
				getFixedF(SIZE_P, Ref(PtNumOnEdge), PtGrpKey);
				//Notice the order POI visitedNode on edge
				unsigned long long pkwd;
				int pid;
				for (int t = 0; t < PtNumOnEdge; t++) {
					getVarE(PT_DIST, Ref(PtDist), PtGrpKey, t);
					int idist = (int)PtDist;
					PtDist = idist;
					getVarE(PT_KWD, &pkwd, PtGrpKey, t);
					getVarE(PT_P, &pid, PtGrpKey, t);
					if ((pkwd&Q.keywords) != Q.keywords) {
						continue;
					}
					else {
						float disti = INFINITY;
						float distj = INFINITY;
						if (vid < NewNodeID) {
							disti = ldist + PtDist;
							if (bothEdge) distj = EdgeDist - PtDist + result[posj];
						}
						else {
							disti = ldist + EdgeDist - PtDist;
							if (bothEdge) distj = PtDist + result[posj];
						}
						//disti = ldist + PtDist;
						//if (bothEdge) distj = EdgeDist - PtDist + result[posj];
						if (distj < disti) disti = distj;


						float sdis = INFINITY;
						if ((vid == qni) && (NewNodeID == qnj)) {
							sdis = fabsf(PtDist - qp.dist_Ni);
						}

						if (disti > sdis) disti = sdis;
						qpair qpa;
						qpa.dist = disti;
						qpa.isPOI = true;
						qpa.qid = pid;
						tpq.push(qpa);
					}
				}
			}
		}
	}
	if(tpq.size()) return tpq.top().dist;
	else return tnm.tmin;
}


void updateT(tpQueryPQ& tpq, tnTmin& tnm, map<int, map<int, vector<float>>>& an, int qid) {
	// Update
	int i, j;
	int fid = EGT[tnm.tnid].father;
	float distN = INFINITY;
	vector<float> distB;
	
	// 计算从当前节点到父节点border的距离以及将相邻兄弟节点加入	
	for (i = 0; i < EGT[fid].borders.size(); i++) {
		int fbid = EGT[fid].borders[i];
		int posi = find(EGT[fid].union_borders.begin(), EGT[fid].union_borders.end(), fbid) - EGT[fid].union_borders.begin();
		float distA = INFINITY;
		//vector<float> tnidDist = an[qid][tnm.tnid];
		for (j = 0; j < EGT[tnm.tnid].borders.size(); j++) {
			int cbid = EGT[tnm.tnid].borders[j];
			int posj = find(EGT[fid].union_borders.begin(), EGT[fid].union_borders.end(), cbid) - EGT[fid].union_borders.begin();

			int index;
			float dist;
			if (posi > posj) {
				index = ((posi + 1)*posi) / 2 + posj;
				dist = EGT[fid].mind[index];
			}
			else {
				index = ((posj + 1)*posj) / 2 + posi;
				dist = EGT[fid].mind[index];
			}
			dist = dist + an[qid][tnm.tnid][j];
			if (dist < distA) distA = dist;
		}
		distB.push_back(distA);
		if (distA < distN) distN = distA;
	}
	an[qid][fid] = distB;

	// 将其他孩子节点也加入进来
	for (i = 0; i < EGT[fid].children.size(); i++) {
		int cid = EGT[fid].children[i];

		if (cid != tnm.tnid) {
			// 计算tnid到cid的距离
			float distNC = INFINITY;
			vector<float> distBC;
			// 计算从当前节点到兄弟节点的距离
			for (j = 0; j < EGT[cid].borders.size(); j++) {
				int cbid = EGT[cid].borders[j];
				int posi = find(EGT[fid].union_borders.begin(), EGT[fid].union_borders.end(), cbid) - EGT[fid].union_borders.begin();
				float distAC = INFINITY;
				for (int k = 0; k < EGT[tnm.tnid].borders.size(); k++) {
					int bid = EGT[tnm.tnid].borders[k];
					int posj = find(EGT[fid].union_borders.begin(), EGT[fid].union_borders.end(), bid) - EGT[fid].union_borders.begin();

					int index;
					float dist;
					if (posi > posj) {
						index = ((posi + 1)*posi) / 2 + posj;
						dist = EGT[fid].mind[index];
					}
					else {
						index = ((posj + 1)*posj) / 2 + posi;
						dist = EGT[fid].mind[index];
					}
					dist = dist + an[qid][tnm.tnid][k];
					if (dist < distAC) distAC = dist;
				}
				distBC.push_back(distAC);
				if (distAC < distNC) distNC = distAC;
			}
			an[qid][cid] = distBC;

			qpair qp;
			qp.isPOI = false;
			qp.qid = cid;
			qp.dist = distNC;
			tpq.push(qp);
		}
	}

	tnm.tmin = distN;
	tnm.tnid = fid;
}


void findNextEG(tpQueryPQ& tpq, vector<int>& all, int qid, int& vcid, float& dist, map<int, map<int, vector<float>>>& an, tnTmin& tnm) {
	int AdjGrpAddr, AdjListSize, NewNodeID, PtGrpKey, PtNumOnEdge;
	unsigned long long sumkwd;
	float EdgeDist, PtDist;
	int i, j, posj;
	int qni = Q.querypts[qid].Ni;
	int qnj = Q.querypts[qid].Nj;
	while (tpq.size() || tnm.tnid) {
		if (tpq.empty()) updateT(tpq, tnm, an, qid);
		qpair qpa = tpq.top();
		tpq.pop();

		if (qpa.dist > tnm.tmin) {
			updateT(tpq, tnm, an, qid);
			tpq.push(qpa);
		}
		else if (qpa.isPOI) {
			if (find(all.begin(),all.end(),qpa.qid) != all.end()) continue;
			//all.push_back(qpa.qid);
			vcid = qpa.qid;
			dist = qpa.dist;
			break;
		}
		else if (!qpa.isPOI) {
			// 两种情况，叶子节点和非叶子节点
			int nid = qpa.qid;
			if (EGT[nid].isleaf) {
				// 通过border计算到内部每个节点的距离，进而访问每条边信息
				vector<float> tVDist;
				//vector<float> tBDist = an[qid][nid];
				for (i = 0; i < EGT[nid].leafnodes.size(); i++) {
					float minD = INFINITY;
					int lid = EGT[nid].leafnodes[i];

					//int size = EGT[nid].borders.size();
					for (j = 0; j < EGT[nid].borders.size(); j++) {
						int pos = j*EGT[nid].leafnodes.size() + i;
						float dist = EGT[nid].mind[pos] + an[qid][nid][j];
						if (dist < minD) minD = dist;
					}
					tVDist.push_back(minD);
				}
				//if ((EGT[nid].unionkwds&Q.keywords) != Q.keywords) continue;
				// 然后对每一个leafnodes进行处理
				for (j = 0; j < EGT[nid].leafnodes.size(); j++) {
					int vid = EGT[nid].leafnodes[j];
					float ldist = tVDist[j];

					AdjGrpAddr = getAdjListGrpAddr(vid);
					getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);
					for (int n = 0; n < AdjListSize; n++) {
						getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, n);
						getVarE(DIST_A, Ref(EdgeDist), AdjGrpAddr, n);
						int iedist = (int)EdgeDist;
						EdgeDist = iedist;
						getVarE(SUMKWD_A, &sumkwd, AdjGrpAddr, n);
						if ((sumkwd&Q.keywords) != Q.keywords) continue;
						unsigned long long NewNodeIDe = NewNodeID;
						//unsigned long long edge = getKey(vide, NewNodeIDe);
						bool bothEdge = false;
						if (find(EGT[nid].leafnodes.begin(), EGT[nid].leafnodes.end(), NewNodeID) != EGT[nid].leafnodes.end()) {

							if (vid > NewNodeID) continue;
							bothEdge = true;
							for (int p = 0; p < EGT[nid].leafnodes.size(); p++) {
								if (EGT[nid].leafnodes[p] == NewNodeID) {
									posj = p;
									break;
								}
							}
						}
						getVarE(PTKEY_A, Ref(PtGrpKey), AdjGrpAddr, n);
						if (PtGrpKey == -1) {
							//cout<<"No POI existed on Edge where Q located."<<endl;
						}
						else {
							nOfEdgeExpended++;
							//getVarE(DIST_A, Ref(EdgeDist), AdjGrpAddr, n);
							getFixedF(SIZE_P, Ref(PtNumOnEdge), PtGrpKey);
							//Notice the order POI visitedNode on edge
							unsigned long long pkwd;
							int pid;
							for (int t = 0; t < PtNumOnEdge; t++) {
								getVarE(PT_DIST, Ref(PtDist), PtGrpKey, t);
								int idist = (int)PtDist;
								PtDist = idist;
								getVarE(PT_KWD, &pkwd, PtGrpKey, t);
								getVarE(PT_P, &pid, PtGrpKey, t);
								if ((pkwd&Q.keywords) != Q.keywords) {
									continue;
								}
								else {
									float disti = INFINITY;
									float distj = INFINITY;
									if (vid < NewNodeID) {
										disti = ldist + PtDist;
										if (bothEdge) distj = EdgeDist - PtDist + tVDist[posj];
									}
									else {
										disti = ldist + EdgeDist - PtDist;
										if (bothEdge) distj = PtDist + tVDist[posj];
									}
									/*disti = ldist + PtDist;
									if (bothEdge) distj = EdgeDist - PtDist + tVDist[posj];*/
									if (distj < disti) disti = distj;


									float sdis = INFINITY;
									if ((vid == qni) && (NewNodeID == qnj)) {
										sdis = fabsf(PtDist - Q.querypts[qid].dist_Ni);
									}

									if (disti > sdis) disti = sdis;
									qpair qpa;
									qpa.dist = disti;
									qpa.isPOI = true;
									qpa.qid = pid;
									tpq.push(qpa);
								}
							}
						}
					}
				}
			}
			else {
				// 将其他孩子节点也加入进来
				//int fid = nid;
				for (i = 0; i < EGT[nid].children.size(); i++) {
					int cid = EGT[nid].children[i];
					// 计算tnid到cid的距离
					float distNC = INFINITY;
					vector<float> distBC;
					// 计算从当前节点到父节点border的距离以及将相邻兄弟节点加入	
					for (j = 0; j < EGT[cid].borders.size(); j++) {
						int cbid = EGT[cid].borders[j];
						int posi = find(EGT[nid].union_borders.begin(), EGT[nid].union_borders.end(), cbid) - EGT[nid].union_borders.begin();
						float distAC = INFINITY;
						for (int k = 0; k < EGT[nid].borders.size(); k++) {
							int bid = EGT[nid].borders[k];
							int posj = find(EGT[nid].union_borders.begin(), EGT[nid].union_borders.end(), bid) - EGT[nid].union_borders.begin();

							int index;
							float dist;
							if (posi > posj) {
								index = ((posi + 1)*posi) / 2 + posj;
								dist = EGT[nid].mind[index];
							}
							else {
								index = ((posj + 1)*posj) / 2 + posi;
								dist = EGT[nid].mind[index];
							}
							dist = dist + an[qid][nid][k];
							if (dist < distAC) distAC = dist;
						}
						distBC.push_back(distAC);
						if (distAC < distNC) distNC = distAC;
					}
					an[qid][cid] = distBC;

					qpair qpa;
					qpa.isPOI = false;
					qpa.qid = cid;
					qpa.dist = distNC;
					tpq.push(qpa);
				}
			}
		}
	}
}

void ANNEG() {
	cout << "start ANNEG" << endl;
	int AdjGrpAddr, AdjListSize, NewNodeID, PtGrpKey, PtNumOnEdge;
	unsigned long long sumkwd;
	float EdgeDist, PtDist;
	// 首先对于每个查询点，找到它对应的最近的VCell;
	int qsize = Q.querypts.size();
	vector<vector<int>> candidate(qsize, vector<int>());//保存每个查询点当前包含关键字的vid

	vector<float> NNDist(qsize, 0); // 记录到所有查询点最近的距离
	vector<float> FNNDist(qsize, 0); // 记录到所有查询点最近的距离
	vector<tnTmin> TnTm(qsize); // 记录Tn 和 Tmin
	map<int, map<int, float>> qTcandidate; // 记录查询点到Candidate的距离

	map<int, map<int, vector<float>>> an;
	map<int, tpQueryPQ> PQ;


	for (int i = 0; i < qsize; i++) {	
		QueryPoint qp = Q.querypts[i];
		if (an.find(i) == an.end()) {
			map<int, vector<float>> mapan;
			mapan.clear();
			an[i] = mapan;

			tpQueryPQ tpq;
			PQ[i] = tpq;
		}
		float minD = findInitial(qp, PQ[i], i, an[i], TnTm[i]);
		qpair qpa;
		qpa.qid = i;
		qpa.dist = minD;
		queryPQ.push(qpa);
	}

	// 不断扩展当前队列直到交集不为空；
	vector<int> common;
	while (noCommon(candidate, common)) {
		// 注意这里弹出来的是不是距离最小
		qpair qpa = queryPQ.top();
		queryPQ.pop();
		int qid = qpa.qid;
		int vcid;
		float vdist;
		findNextEG(PQ[qid], candidate[qid], qid, vcid, vdist, an, TnTm[qid]);
		if (vcid == 25803) {
			cout << vcid<< " "<< qid << " " << vdist << endl;
		}
		qpa.dist = vdist;
		queryPQ.push(qpa);
		/*if (candidate[qid].find(vcid) == candidate[qid].end()) {
			candidate[qid].insert(vcid);
		}*/
		if (find(candidate[qid].begin(), candidate[qid].end(),vcid) == candidate[qid].end()) {
			candidate[qid].push_back(vcid);
		}

		if (qTcandidate.find(qid) == qTcandidate.end()) {
			map<int, float> tp;
			tp.clear();
			tp[vcid] = vdist;
			qTcandidate[qid] = tp;
			NNDist[qid] = vdist;
			FNNDist[qid] = vdist;
		}
		else {
			if (qTcandidate[qid].find(vcid) == qTcandidate[qid].end()) {
				qTcandidate[qid][vcid] = vdist;
				FNNDist[qid] = vdist;
			}		
		}	
	}

	// 当前已经有共同的了，那么就可以过滤Candidate中的元素了
	//1:构建S集合
	set<int> S;
	//vector<unordered_set<int>>::iterator iac = candidate;
	for (int k = 0; k < candidate.size(); k++) {
		for (int t = 0; t < candidate[k].size(); t++) {
			int tid = candidate[k][t];
			if (S.find(tid) == S.end()) S.insert(tid);
		}
	}
	
	//2:计算aggregatedist
	set<int> candSet;
	float topKAggdist = -1;
	int topKId = -1, topKPos = 0;
	for (int t=0; t < common.size(); t++) {
		int pid = common[t];
		float aggDist = 0;
		for (int k = 0; k < qsize; k++) {
			if (isSumDist) aggDist += qTcandidate[k][pid];
			else {
				if (aggDist < qTcandidate[k][pid]) aggDist = qTcandidate[k][pid];
			}
		}
		candidateAggPoint ca;
		ca.distance = aggDist;
		ca.poid = pid;
		if (aggDist > topKAggdist) {
			topKAggdist = aggDist;
			topKId = pid;
			topKPos = t;
		}
		candSet.insert(pid);
		rs.topK.push_back(ca);
	}

	while (S.size()) {
		//cout << "S.size() is : " << S.size() << endl;		
		qpair qpa = queryPQ.top();
		queryPQ.pop();
		int qid = qpa.qid;
		int vcid;
		float vdist;
		findNextEG(PQ[qid], candidate[qid], qid, vcid, vdist, an, TnTm[qid]);

		qpa.dist = vdist;
		qpa.qid = qid;
		queryPQ.push(qpa);
		if (vcid == 25803) {
			cout << vcid << " " << qid << " " << vdist << endl;
		}
		if (qTcandidate.find(qid) == qTcandidate.end()) {
			map<int, float> tp;
			tp.clear();
			tp[vcid] = vdist;
			qTcandidate[qid] = tp;
			NNDist[qid] = vdist;
			FNNDist[qid] = vdist;
		}
		else {
			if (qTcandidate[qid].find(vcid) == qTcandidate[qid].end()) {
				qTcandidate[qid][vcid] = vdist;
				FNNDist[qid] = vdist;
			}
		}
		// 注意：这里是不是要把vcid加入Candidate中
		// candidate[qid].insert(vcid);
		// 计算dist
		float tdist = 0;
		for (int k = 0; k < candidate.size(); k++) {
			vector<int> tpSet = candidate[k];
			if (isSumDist) {
				if (find(tpSet.begin(), tpSet.end(), vcid) == tpSet.end()) {
					tdist = tdist + NNDist[k];
				}
				else {
					float distT = qTcandidate[k][vcid];
					tdist = tdist + qTcandidate[k][vcid];
				}
			}
			else {
				if (find(tpSet.begin(), tpSet.end(), vcid) == tpSet.end()) {
					if (tdist < FNNDist[k]) tdist = FNNDist[k];
				}
				else {
					if (tdist < qTcandidate[k][vcid]) tdist = qTcandidate[k][vcid];
				}
			}
		}
		if (tdist > topKAggdist) {
			set<int> SPlus;
			for (int k = 0; k < candidate.size(); k++) {
				vector<int> tpSet = candidate[k];
				if (find(tpSet.begin(), tpSet.end(), vcid) != tpSet.end()) {
					//unordered_set<int>::iterator its = tpSet.begin();
					for (int t = 0; t<tpSet.size(); t++) {
						int id = tpSet[t];
						if (id != vcid) {
							if (SPlus.find(id) == SPlus.end()) SPlus.insert(id);
						}
						else break;
					}
				}
			}
			// 过滤S
			set<int>::iterator itS = S.begin();
			set<int> tempS;
			int ssize = S.size();
			for (; itS != S.end(); itS++) {
				int fid = *itS;
				if (SPlus.find(fid) != SPlus.end()) tempS.insert(fid);
			}
			S.clear();
			//S = tempS;

			//继续优化
			//set<int> tempS;
			//tempS = S;
			//S.clear();
			itS = tempS.begin();
			for (; itS != tempS.end(); itS++) {
				int tid = *itS;
				float allDist = 0;
				for (int k = 0; k < candidate.size(); k++) {
					vector<int> tpSet = candidate[k];
					if (isSumDist) {
						if (find(tpSet.begin(), tpSet.end(), tid) == tpSet.end()) {
							allDist = allDist + FNNDist[k];
						}
						else {
							float distT = qTcandidate[k][tid];
							allDist = allDist + qTcandidate[k][tid];
						}
					}
					else {
						if (find(tpSet.begin(), tpSet.end(), vcid) == tpSet.end()) {
							if (allDist < FNNDist[k]) allDist = FNNDist[k];
						}
						else {
							if (allDist < qTcandidate[k][tid]) allDist = qTcandidate[k][tid];
						}
					}
				}
				if (candSet.find(tid) == candSet.end()) {
					if (allDist < topKAggdist) S.insert(tid);
				}			
			}
			
			candidate[qid].push_back(vcid);
		}
		else {
			candidate[qid].push_back(vcid);
			bool isVisitedByAll = true;
			float adist = 0;
			for (int k = 0; k < candidate.size(); k++) {
				vector<int> tpSet = candidate[k];
				if (find(tpSet.begin(),tpSet.end(),vcid) == tpSet.end()) {
					isVisitedByAll = false;
					break;
				}
				else {
					if (isSumDist) {
						adist = adist + qTcandidate[k][vcid];
					}
					else {
						if (adist < qTcandidate[k][vcid]) adist = qTcandidate[k][vcid];
					}
				}
			}
			
			if (isVisitedByAll) {				
				if (topKAggdist > adist) {
					S.erase(topKId);

					candSet.erase(topKId);
					candSet.insert(vcid);
					rs.topK[topKPos].poid = vcid;
					rs.topK[topKPos].distance = adist;
					
					for (int l = 0; l < rs.topK.size(); l++) {
						if (0 == l) {
							topKPos = l;
							topKAggdist = rs.topK[l].distance;
							topKId = rs.topK[l].poid;
						}
						else {
							if (topKAggdist < rs.topK[l].distance) {
								topKPos = l;
								topKAggdist = rs.topK[l].distance;
								topKId = rs.topK[l].poid;
							}
						}
					}
				}
			}
		}
		//candidate[qid].insert(vcid);
	}

	/*set<int> ::iterator itSet = S.begin();
	for (; itSet != S.end(); itSet++) {
		candidateAggPoint cp;
		cp.poid = *itSet;
		rs.topK.push_back(cp);
		cout << cp.poid << " ";
	}
	cout << endl;*/
	int sumid = 0;
	for (int i = 0; i < rs.topK.size(); i++) {
		sumid = sumid + rs.topK[i].poid;
	}
	rs.sumpid = sumid;
	nOfPageAccessed = printPageAccess(-1);
	for (int l = 0; l < rs.topK.size(); l++) {
		cout << rs.topK[l].poid << " " << rs.topK[l].nodei << " " << rs.topK[l].nodej << " " << rs.topK[l].distance << endl;
	}

	//printf("The result of TA distance is: %f\n", rs.kthDist);
	printf("The ANNEG sumid is: %d\n", rs.sumpid);
	//cout << "VANN result is: " << rtPOI << " " << aggDist << endl;
}

void getConstantKwds(int totalNumberOfNodes, int number, vector<unsigned long long>& inkeys)
{
	std::vector<unsigned long long> keys;
	keys.reserve(totalNumberOfNodes);
	std::bitset<MAX_KEYWORDS> keywordsSet;
	srand((unsigned)time(NULL));
	while (totalNumberOfNodes--) {
		keywordsSet.reset();
		while (keywordsSet.count() < number)
		{
			int index;
			if (keywordsSet.count() < 6) {

				// index = random()%8;
				index = rand() % 16;
			}
			else {
				//index = random() % 20;
				index = rand() % 32;
			}
			keywordsSet.set(index);

		}

		//while (keywords_set.count() < number)
		//{
		//	int index;
		//	if (keywords_set.count() < 6) {
		//		//index = random()%8;
		//		index = rand() % 8;
		//	}
		//	else {
		//		//index = random() % 20;
		//		index = rand() % 20;
		//	}
		//	keywords_set.set(index + 22);
		//}


		keys.push_back(keywordsSet.to_ullong());
	}
	inkeys.assign(keys.begin(), keys.end());
	//keys;

}

int qk = 3;//查询关键字个数
int nOfTest = 20;
int k = 10;

struct querycand {
	int nodei;
	int nodej;
	float length;
	bool visited;
};
map<int, querycand>  qc;

void geneQuery(string prxfilename) {
	string name;
	name.clear();
	name = prxfilename + "\\partAddr";
	string inFile = prxfilename + "\\candquery";
	string outFile = prxfilename + "\\queryfile";
	//sprintf(tmpFileName, "%s\\partAddr", fileprefix);
	NodeNum = partAddrLoad(name.c_str(), paID);
	//NodeNum = paID.size();
	// read info from java transform file, 
	// format: edgeid nodei nodej length

	srand((unsigned)time(NULL));
	vector<unsigned long long> inkey(nOfTest, 0);
	getConstantKwds(nOfTest, qk, inkey);
	ifstream iFile(inFile.c_str());
	ofstream oFile(outFile.c_str());
	int loop = 0;
	while (!iFile.eof())
	{
		string line;
		getline(iFile, line);
		if (line == "")
			continue;
		istringstream iss(line);
		unsigned long long edgeid;
		int nodei, nodej, length;
		//float length;
		iss >> edgeid >> nodei >> nodej >> length;
		if (paID[nodei].part != paID[nodej].part) continue;
		querycand qu;
		qu.nodei = nodei;
		qu.nodej = nodej;
		qu.length = length;
		qu.visited = false;
		qc[loop] = qu;
		loop++;
	}
	int size = qc.size();
	// generate Q.keywords
	int l = 0;
	while (l < nOfTest) {
		/*bitset<MAX_KEYWORDN> keywords_set;
		keywords_set.reset();
		while (keywords_set.count() != qk) {
		int position = rand() % MAX_KEYWORDN;
		keywords_set.set(position);
		}*/
		//unsigned long long kwd = keywords_set.to_ullong();
		unsigned long long kwd = inkey[l];
		oFile << kwd << " " << k;
		// generate Q.querypts
		for (int i = 0; i < k; ) {
			int ni, nj;
			int disti;
			int position = rand() % size;
			querycand qu = qc[position];
			if (qu.visited) continue;
			i++;
			qu.visited = true;
			int randnum = 0;
			while (randnum == 0 || randnum == RAND_MAX) {
				randnum = rand();
			}
			disti = (int)((randnum*qu.length) / RAND_MAX);
			oFile << "," << qu.nodei << " " << qu.nodej << " " << qu.length << " " << disti;
		}
		oFile << endl;
		l++;
	}
	iFile.close();
	oFile.close();
}


void genekwds(string prxfilename) {
	string name;
	name.clear();

	name = prxfilename + "\\partAddr";
	//sprintf(tmpFileName, "%s\\partAddr", fileprefix);
	NodeNum = partAddrLoad(name.c_str(), paID);
	//NodeNum = paID.size();
	// read info from java transform file, 
	// format: edgeid nodei nodej length
	//string inFile = prxfilename + "\\candquery";
	string outFile = prxfilename + "\\keywordsfile";

	//ifstream iFile(inFile.c_str());
	ofstream oFile(outFile.c_str());
	//int loop = 0;
	set<unsigned long long> kwd;
	srand((unsigned)time(NULL));
	for (int loop = 0; ; loop++) {
		int id = rand() % NodeNum;
		unsigned long long vide = id;
		int AdjGrpAddr = getAdjListGrpAddr(id);
		int AdjListSize, NewNodeID, PtGrpKey, PtNumOnEdge;
		unsigned long long sumkwd;
		getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);
		for (int n = 0; n < AdjListSize; n++) {

			getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, n);
			getVarE(PTKEY_A, Ref(PtGrpKey), AdjGrpAddr, n);
			unsigned long long NewNodeIDe = NewNodeID;
			unsigned long long edge = getKey(vide, NewNodeIDe);
			// bool isonedge;
			if (PtGrpKey == -1) {
				//cout<<"No POI existed on Edge where Q located."<<endl;
			}
			else {
				nOfEdgeExpended++;
				//getVarE(DIST_A, Ref(EdgeDist), AdjGrpAddr, n);
				getFixedF(SIZE_P, Ref(PtNumOnEdge), PtGrpKey);
				//Notice the order POI visitedNode on edge
				unsigned long long pkwd;
				int pid;
				for (int t = 0; t < PtNumOnEdge; t++) {
					getVarE(PT_KWD, &pkwd, PtGrpKey, t);
					bitset<MAX_KEYWORDN> kwdbit(pkwd);
					int ct = kwdbit.count();
					if (kwdbit.count() > 5) {
						if (kwd.count(pkwd) == 0) {
							kwd.insert(pkwd);
						}
					}
				}
			}
		}
		if (kwd.size() > 100) break;
	}

	//iFile.close();
	//output the kwds
	set<unsigned long long>::iterator it = kwd.begin();
	for (; it != kwd.end(); it++) {
		unsigned long long temp = *it;
		oFile << temp << endl;
	}
	oFile.close();
}
//*********** start of TKDE2005
// compute the Euclidean distance
float getDist(float x1, float y1, float x2, float y2) {
	return float(sqrt((x2 - x1)*(x2 - x1) + (y2 - y1)*(y2 - y1)));
}
// compute the network distance 
// vj: the poi point on the edge
// onSameEdge: whether this edge of VJ is same with the query point locateded in
// eKdist: the length of this edge

inline float getNetworkDist(float vJ, BitStore& onSameEdge, float eKdist) {
	float dist = 0;
	for (int sp = 0; sp<Q.k; sp++) {
		float distL = partdists[sp][0] + vJ;
		float distR = partdists[sp][1] + eKdist - vJ;
		float distT = min(distL, distR);
		if (onSameEdge[sp]) {
			float distQ = ValAbs(Q.querypts[sp].dist_Ni - vJ);
			if (distQ<distT) distT = distQ;
		}

		compdist[sp] = distT;	// for log (log the original one) !
								//if (isWeightUse) distT = distT*weights[sp];

		if (isSumDist)
			dist += distT;
		else
			dist = max(distT, dist);
	}
	return dist;
}

inline void InitDQ(DistQueue& dQ) {
	dQ.empty();
	elem_map.clear();
	//	while (!dQ.empty()) dQ.pop();	// clear kNN-dist heap
}


// 0 large 1 small // get a possible optimal position for in this edge
inline float getOptPos(int NodeID, int NewNodeID, float eKdist, float& bestPos) {
	float vJ, bestVal, tmpPos, tmpVal;
	int sid = 0, eid = 1;
	//if (NewNodeID<NodeID) { sid = 1; eid = 0; }

	for (int sp = 0; sp<Q.k; sp++) {
		partdists[sp][0] = partdists[sp][1] = MAX_DIST;
		/*if (DistMaps[sp].count(NodeID)>0)
		partdists[sp][sid] = DistMaps[sp][NodeID];
		if (DistMaps[sp].count(NewNodeID)>0)
		partdists[sp][eid] = DistMaps[sp][NewNodeID];*/
		if (NewNodeID < NodeID) {
			if (DistMaps[sp].count(NodeID)>0) partdists[sp][1] = DistMaps[sp][NodeID];
			//else printf("Dist Error in UpdatePoints\n");
			if (DistMaps[sp].count(NewNodeID)>0) partdists[sp][0] = DistMaps[sp][NewNodeID];
			//else printf("Dist Error in UpdatePoints\n");
			//int qNi = Q.querypts[sp].Ni, qNj = Q.querypts[sp].Nj;
		}
		else {
			if (DistMaps[sp].count(NodeID)>0) partdists[sp][0] = DistMaps[sp][NodeID];
			//else printf("Dist Error in UpdatePoints\n");
			if (DistMaps[sp].count(NewNodeID)>0) partdists[sp][1] = DistMaps[sp][NewNodeID];
			//else printf("Dist Error in UpdatePoints\n");
		}
		int qNi = Q.querypts[sp].Ni, qNj = Q.querypts[sp].Nj;
		onSameEdge[sp] = (NodeID == qNi&&NewNodeID == qNj) || (NodeID == qNj&&NewNodeID == qNi);
	}

	// for isSumDist only
	bestPos = 0;
	bestVal = getNetworkDist(bestPos, onSameEdge, eKdist);

	tmpPos = eKdist;
	tmpVal = getNetworkDist(tmpPos, onSameEdge, eKdist);
	if (tmpVal<bestVal) { bestPos = tmpPos; bestVal = tmpVal; }

	int NUM_STEPS = 100;
	if (!isWeightUse) {
		if (isSumDist) {
			for (int sp = 0; sp<Q.k; sp++) {
				if (onSameEdge[sp]) {
					tmpPos = Q.querypts[sp].dist_Ni;
					tmpVal = getNetworkDist(tmpPos, onSameEdge, eKdist);
					if (tmpVal<bestVal) { bestPos = tmpPos; bestVal = tmpVal; }
				}
			}
		}
		else {
			// can find a loose lb for ...
			//bestVal-=eKdist;
			for (int j = 0; j<NUM_STEPS; j++) {	// scan
				tmpPos = j*eKdist / (NUM_STEPS - 1);
				tmpVal = getNetworkDist(tmpPos, onSameEdge, eKdist);
				if (tmpVal<bestVal) { bestPos = tmpPos; bestVal = tmpVal; }
			}
		}
	}
	else {
		for (int j = 0; j<NUM_STEPS; j++) {	// scan
			tmpPos = j*eKdist / (NUM_STEPS - 1);
			tmpVal = getNetworkDist(tmpPos, onSameEdge, eKdist);
			if (tmpVal<bestVal) { bestPos = tmpPos; bestVal = tmpVal; }
		}
	}
	return bestVal;
}


bool UpdatePoints(int NodeID, int NewNodeID, int PtGrpAddr, float eKdist) {
	float vJ;
	bool hasChanged = false;
	unsigned long long sumkwd;
	int sid = 0, eid = 1;
	//if (NewNodeID<NodeID) { sid = 1; eid = 0; }

	for (int sp = 0; sp<Q.k; sp++) {
		partdists[sp][0] = partdists[sp][1] = MAX_DIST;
		if (NewNodeID < NodeID) {
			if (DistMaps[sp].count(NodeID)>0) partdists[sp][1] = DistMaps[sp][NodeID];
			//else printf("Dist Error in UpdatePoints\n");
			if (DistMaps[sp].count(NewNodeID)>0) partdists[sp][0] = DistMaps[sp][NewNodeID];
			//else printf("Dist Error in UpdatePoints\n");
			//int qNi = Q.querypts[sp].Ni, qNj = Q.querypts[sp].Nj;
		}
		else {
			if (DistMaps[sp].count(NodeID)>0) partdists[sp][0] = DistMaps[sp][NodeID];
			//else printf("Dist Error in UpdatePoints\n");
			if (DistMaps[sp].count(NewNodeID)>0) partdists[sp][1] = DistMaps[sp][NewNodeID];
			//else printf("Dist Error in UpdatePoints\n");
		}
		/*if (distmaps[sp].count(nodeid)>0) partdists[sp][sid] = distmaps[sp][nodeid];
		else printf("dist error in updatepoints\n");
		if (distmaps[sp].count(newnodeid)>0) partdists[sp][eid] = distmaps[sp][newnodeid];
		else printf("dist error in updatepoints\n");*/
		int qNi = Q.querypts[sp].Ni, qNj = Q.querypts[sp].Nj;
		onSameEdge[sp] = (NodeID == qNi&&NewNodeID == qNj) || (NodeID == qNj&&NewNodeID == qNi);
	}


	int PtGrpSize, dummy;
	//PtGrpAddr = pointQuery(PtTree, PtGrpKey, dummy);
	nOfEdgeExpended++;
	getFixedF(SIZE_P, Ref(PtGrpSize), PtGrpAddr);
	for (int j = 0; j<PtGrpSize; j++) {	// scan
		int pid = 0;
		getVarE(PT_P, Ref(pid), PtGrpAddr, j);
		//printf("The pid visited is:%d\n", pid);

		getVarE(PT_DIST, Ref(vJ), PtGrpAddr, j);
		int ipdist = (int)vJ;
		vJ = ipdist;
		getVarE(PT_KWD, Ref(sumkwd), PtGrpAddr, j);
		if ((sumkwd&Q.keywords) != Q.keywords) continue;
		nodeleft = NodeID;
		noderight = NewNodeID;
		keyw = sumkwd;
		interkeyw = sumkwd&Q.keywords;

		float dist = getNetworkDist(vJ, onSameEdge, eKdist);

		//if (dist < bestdist) {
		//	bestdist = dist;
		//	rs.distance = bestdist;
		//	rs.inter = (sumkwd&q.keywords);
		//	rs.kwdnode = sumkwd;
		//	rs.nodei = nodeid;
		//	rs.nodej = newnodeid;
		//	//rs.poid = pid;
		//}
		
		if (dist < rs.kthDist) {
			// 两种情况，如果已经有k个则更新，否则，直接加入
			//bestdist = dist;
			vector<candidateAggPoint> ::iterator it = rs.topK.begin();			
			for (int lp = 0; it != rs.topK.end(); it++) {
				candidateAggPoint caplp = *it;
				if (caplp.poid == pid) return false;
			}

			if ((rs.topK.size() + 1) <= rs.nOfAggPoint) {
				candidateAggPoint cap;
				cap.distance = dist;
				cap.poid = pid;
				cap.nodei = NodeID;
				cap.nodej = NewNodeID;
				rs.topK.push_back(cap);
			}
			else {
				// 找到最大的那个，判断是否需要更新
				//vector<candidateAggPoint> ::iterator itcap = rs.topK.begin();
				float maxdist = -1; int maxindex = -1;
				for (int lp = 0; lp < rs.topK.size();  lp++) {
					candidateAggPoint caplp = rs.topK[lp];
					if (maxdist < caplp.distance) {
						maxdist = caplp.distance;
						maxindex = lp;
					}
				}
				//rs.kthDist = maxdist;
				if (maxdist > dist) {
					rs.topK[maxindex].distance = dist;
					rs.topK[maxindex].poid = pid;
					rs.topK[maxindex].nodei = NodeID;
					rs.topK[maxindex].nodej = NewNodeID;
					//rs.kthDist = dist;
				}
				rs.kthDist = -1;
				for (int lp = 0; lp < rs.topK.size(); lp++) {
					candidateAggPoint caplp = rs.topK[lp];
					if (rs.kthDist < caplp.distance) {
						rs.kthDist = caplp.distance;
						//maxindex = lp;
					}
				}
			}
			rs.inter = (sumkwd&Q.keywords);
			rs.kwdnode = sumkwd;
		}
		//UpdateOnePt(vJ, hasChanged, onSameEdge, eKdist, pid);
	}


	//if (bestdist<MAX_DIST) {PrintElapsed();	exit(0);}
	/*if (hasChanged)
	printf("c: %d %d %f\n",NodeID,NewNodeID,eKdist);*/
	return hasChanged;
}

// top-k
// get the possible minimum distance to this edge and return the value
inline float getMinOptPos(int NodeID, int NewNodeID, float eKdist) {
	float dist = 0, mincpdist, ldist, rdist;
	for (int sp = 0; sp<Q.k; sp++) {
		mincpdist = MAX_DIST;
		ldist = rdist = MAX_DIST;
		if (DistMaps[sp].count(NodeID)>0) ldist = DistMaps[sp][NodeID];
		if (DistMaps[sp].count(NewNodeID)>0) rdist = DistMaps[sp][NewNodeID];
		if (ldist<MAX_DIST) {
			if (rdist<MAX_DIST)
				mincpdist = min(ldist, rdist);
			else
				mincpdist = max(0, ldist - eKdist);
		}
		else {
			if (rdist<MAX_DIST)
				mincpdist = max(0, rdist - eKdist);
			else
				mincpdist = 0;
		}
		if (onSameEdge[sp]) mincpdist = 0;
		mincpdist = max(0, mincpdist);

		//if (isWeightUse) mincpdist = mincpdist*weights[sp];
		if (isSumDist)
			dist += mincpdist;
		else
			dist = max(mincpdist, dist);
	}
	return dist;
}


struct RgnType {
	float partial_dist;
	int crash;
};

typedef map<int, RgnType> REGIONMAP;

// memory requirement: r bitmap and r temp diststore
void ConcurrentExpansion(StepQueue& sQ) {
	//int MaxHeapSize = 0, AggPopSize = 0;
	REGIONMAP epsNbrList;
	BitStore epsBits;
	int AdjListSize, NewNodeID, AdjGrpAddr, PtGrpKey;
	float eKdist, xVal, yVal;
	unsigned long long sumkwd;
	// initialize variables
	//if (!isEuclidSpace) return;
	epsBits.assign(NodeNum, false);
	int maxNbrSize = 0;
	while (!sQ.empty()) {
		//if (MaxHeapSize<sQ.size()) MaxHeapSize = sQ.size();
		StepEvent event = sQ.top();
		sQ.pop();	//AggPopSize++;

		int NodeID = event.node;
		int id = event.ClusID;

		if (DistMaps[id].count(NodeID)>0) continue;	// already found
		DistMaps[id][NodeID] = event.dist;

		float topbound = event.dist;	// change here !
										//if (isWeightUse) topbound = topbound*weights[id];
		if (topbound >= rs.kthDist) break;	// for both S-dist and M-dist: bound almost correct 

		AdjGrpAddr = getAdjListGrpAddr(NodeID);
		getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);	// read # entries


															//maxNbrSize = max(maxNbrSize, epsNbrList.size());
		float epsilon = (isSumDist) ? (rs.kthDist / Q.k) : (rs.kthDist);
		if (epsilon>topbound) { 	// any bug ?
			if (epsBits[NodeID] == false) {
				epsBits[NodeID] = true;
				epsNbrList[NodeID].crash = 0;
				epsNbrList[NodeID].partial_dist = 0;
			}
		}

		if (epsNbrList.count(NodeID)>0) {
			RgnType& rgt = epsNbrList[NodeID];
			rgt.crash += 1;	// update crash
			bool willErase = (rgt.crash >= Q.k);

			float curcpdist = event.dist;
			//if (isWeightUse) curcpdist = curcpdist*weights[id];
			if (isSumDist) {	// update cur dist and check if need prune
				rgt.partial_dist += curcpdist;
				//				if (!willErase&&!isWeightUse) 
				//					willErase=((Q.k-rgt.crash)*event.dist+rgt.partial_dist>=bestdist);
			}
			else {	// update cur dist and check if need prune
				rgt.partial_dist = max(curcpdist, rgt.partial_dist);
				//				if (!willErase&&!isWeightUse) 
				//					willErase=(rgt.partial_dist>=bestdist);	// current lb
			}

			// not useful at all
			if (!willErase) { // correct if maxedgedist used ??
				float curXdist = rgt.partial_dist;
				for (int s = 0; s<Q.k; s++)
					if (DistMaps[s].count(NodeID) == 0) {
						// float tmpdist = getDist(xVal, yVal, M_xcrd[s], M_ycrd[s]);
						float tmpdist = 0;
						tmpdist = max(tmpdist, event.dist);
						//tmpdist=event.dist;	// i.e., Euclidean bounds not used

						//if (isWeightUse) tmpdist = tmpdist*weights[s];
						if (isSumDist)
							curXdist += tmpdist;
						else
							curXdist = max(tmpdist, curXdist);
					}
				if (curXdist >= rs.kthDist) willErase = true;
			}
			if (willErase) {
				// print info.
				/*for (int s=0;s<Q.k;s++)
				if (DistMaps[s].count(NodeID)==0)
				if (getDist(xVal,yVal,M_xcrd[s],M_ycrd[s])>event.dist)
				printf("%d %f %f\n",NodeID,event.dist,
				getDist(xVal,yVal,M_xcrd[s],M_ycrd[s]));*/
				epsNbrList.erase(NodeID);
			}
		}

		if (rs.kthDist<INFINITE_MAX) {	// at least one found
			if (epsNbrList.size() == 0) break;	// all pruned => exit
		}

		for (int z = 0; z<AdjListSize; z++) {
			getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, z);
			getVarE(DIST_A, Ref(eKdist), AdjGrpAddr, z);
			getVarE(SUMKWD_A, Ref(sumkwd), AdjGrpAddr, z);
			int iedist = (int)eKdist;
			eKdist = iedist;
			nOfSEdgeExpended++;
			// getVarE(DIST_A, Ref(eKdist), AdjGrpAddr, z);
			if (DistMaps[id].count(NewNodeID) > 0) continue;
			StepEvent newevent = event;	// copy ...
			newevent.node = NewNodeID;
			newevent.ClusID = event.ClusID;
			newevent.dist = event.dist + eKdist;
			if (DistMaps[id].count(NewNodeID) == 0) sQ.push(newevent);	// propagation
			if ((sumkwd&Q.keywords) != Q.keywords) continue;
			// if error, add cond. to (... && not on same edge) [sp]
			bool needUpdate = true;
			//for (int sp = 0; sp < Q.k; sp++) {
			//	if (DistMaps[sp].count(NodeID) == 0 || DistMaps[sp].count(NewNodeID) == 0) {
			//		needUpdate = false;
			//		break;
			//	}
			//	//needUpdate = false;
			//}
			for (int sp = 0; sp<Q.k; sp++)
				if (DistMaps[sp].count(NodeID) == 0 && DistMaps[sp].count(NewNodeID) == 0)
					needUpdate = false;

			if (needUpdate&&isNNquery) {
				float tmpposition;
				float bestVal = getOptPos(NodeID, NewNodeID, eKdist, tmpposition);
				if (bestVal >= rs.kthDist) needUpdate = false;
			}
			if (!needUpdate) continue;

			getVarE(PTKEY_A, Ref(PtGrpKey), AdjGrpAddr, z);
			if (PtGrpKey >= 0) {	// valid PtGrpKey  (-1 for invalid key)
				bool hasChanged = UpdatePoints(NodeID, NewNodeID, PtGrpKey, eKdist);
			}
		}
	}
	//printf("Heap: max_size %d, pop_size %d\n", MaxHeapSize, AggPopSize);
	//printf("bestdist: %f\n", bestdist);
	//if (!sQ.empty()) printf("topdist: %f\n", sQ.top().dist);
	int totalmapsize = 0;
	for (int sp = 0; sp<Q.k; sp++) {
		//printf("%d) td_sz: %d\n",sp,DistMaps[sp].size());
		totalmapsize += DistMaps[sp].size();
	}
	//printf("totalmapsize: %d, maxNbrSz: %d\n", totalmapsize, maxNbrSize);
	//rs.distance = INFINITE_MAX;
	//rs.poid = -1;

	/*if (dQ_graph.begin() != dQ_graph.end()) {
	rs.distance = dQ_graph.begin()->dist;
	rs.poid = dQ_graph.begin()->id;
	}*/

	nOfPageAccessed = printPageAccess(-1);
	if (rs.topK.size() != rs.nOfAggPoint) cout << "Error in Top-k" << endl;
	int sumid = 0;
	for (int i = 0; i < rs.topK.size(); i++) {
		sumid = sumid + rs.topK[i].poid;
	}
	rs.sumpid = sumid;
	//printf("The result of CE distance is: %f\n", rs.kthDist);
	for (int l = 0; l < rs.topK.size(); l++) {
		cout << rs.topK[l].poid << " " << rs.topK[l].nodei << " " << rs.topK[l].nodej << " " << rs.topK[l].distance << endl;
	}

	printf("The sumid is: %d\n", rs.sumpid);

	//printf("The result of CE oid is: %d\n", rs.poid);
	//printf("The result of CE pageaccessed is: %I64d\n", nOfPageAccessed);
	//printf("The result of CE edgeexpand is: %d\n", nOfEdgeExpended);
	//printf("The result of CE edgeSexpand is: %I64d\n", nOfSEdgeExpended);
	//printf("The result of CE  nodei is: %d\n", rs.nodei);
	//printf("The result of CE  nodej is: %d\n", rs.nodej);
	//printf("The result of CE distance is: %f\n", rs.distance);
	/*printf("The result of CE oid is: %d\n", rs.poid);
	printf("The result of CE edgeexpand is: %d\n", nOfEdgeExpended);
	printf("The result of CE  nodei is: %d\n", rs.nodei);
	printf("The result of CE  nodej is: %d\n", rs.nodej);*/
	//printf("The result of CE  kwdnode is: %llu\n", rs.kwdnode);
	//printf("The result of CE  interkew is: %llu\n", rs.inter);
	//printf("The result of CE  query is: %llu\n", Q.keywords);
}
// compute the distance between current node to the dest with the A* 

float A_star(StepQueue& aQ, BitStore& isVisited, DISTMAP& curdistmap, int dest, int& PopSize, int& VisitedSize) {
	// gdist: from src to cur ; hdist: from cur to dist
	float x_dest, y_dest, x_cur, y_cur;
	int TmpAdjGrpAddr = getAdjListGrpAddr(dest);
	//getFixedF(XCRD_A, Ref(x_dest), TmpAdjGrpAddr);
	//getFixedF(YCRD_A, Ref(y_dest), TmpAdjGrpAddr);

	while (!aQ.empty()) {
		StepEvent event = aQ.top();
		aQ.pop();	PopSize++;

		int NodeID = event.node;

		if (isVisited[NodeID]) {
			if (curdistmap[NodeID] > event.dist) curdistmap[NodeID] = event.dist;
			continue;
		}
		isVisited[NodeID] = true;
		VisitedSize++;
		curdistmap[NodeID] = event.dist;	// only gdist means the real dist. from src. !!!

		float eKdist;
		int AdjListSize, NewNodeID, AdjGrpAddr;
		AdjGrpAddr = getAdjListGrpAddr(NodeID);
		getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);	// read # entries
		for (int z = 0; z<AdjListSize; z++) {
			getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, z);
			getVarE(DIST_A, Ref(eKdist), AdjGrpAddr, z);
			int iedist = eKdist;
			eKdist = iedist;
			if (isVisited[NewNodeID]) continue;
			int idist = (int)eKdist;
			eKdist = idist;
			nOfSEdgeExpended++;
			//StepEvent newevent = event;	// copy ...
			StepEvent newevent;
			newevent.ClusID = event.ClusID;
			newevent.node = NewNodeID;
			//newevent.gdist = event.gdist + eKdist;
			//newevent.hdist = 0;

			//TmpAdjGrpAddr = getAdjListGrpAddr(NewNodeID);
			//getFixedF(XCRD_A, Ref(x_cur), TmpAdjGrpAddr);
			//getFixedF(YCRD_A, Ref(y_cur), TmpAdjGrpAddr);
			//newevent.xc = x_cur;		
			//newevent.yc = y_cur;

			//if (isEuclidSpace) newevent.hdist = getDist(x_cur, y_cur, x_dest, y_dest);
			newevent.dist = event.dist + eKdist;

			// pathmax equation for non-monotonic heuristic ?
			if (newevent.dist<event.dist) newevent.dist = event.dist;
			//if (isVisited[NewNodeID] == false) aQ.push(newevent);
			aQ.push(newevent);
			// propagation		
		}
		if (NodeID == dest) {
			float dis = event.dist;
			//curdistmap[dest] = dis;
			return dis;
		}

	}
	return MAX_DIST;
}



struct ValuePair {
	float value;
	int id;
};

FastArray<ValuePair> covernodeset;

void Repair_astar(StepQueue& aQ, BitStore& isVisited, int dest) {
	int tsize = 0;
	int size = aQ.size();
	StepEvent* tmpAry = new StepEvent[aQ.size()];

	float x_dest, y_dest, x_cur, y_cur;
	int TmpAdjGrpAddr = getAdjListGrpAddr(dest);
	//getFixedF(XCRD_A, Ref(x_dest), TmpAdjGrpAddr);
	//getFixedF(YCRD_A, Ref(y_dest), TmpAdjGrpAddr);

	while (!aQ.empty()) {
		StepEvent event = aQ.top();
		aQ.pop();
		if (isVisited[event.node]) continue;
		isVisited[event.node] = true;
		// assume xc yc fields initialized by the caller !
		event.hdist = 0;	// for Dijkstra
							//if (isEuclidSpace) event.hdist = getDist(x_dest, y_dest, event.xc, event.yc);
		event.dist = event.gdist + event.hdist;
		tmpAry[tsize] = event;
		tsize++;
	}
	for (int i = 0; i<tsize; i++) aQ.push(tmpAry[i]);
	delete[] tmpAry;
}

float dijkstra(vector<StepEvent> se, int nodej) {
	// init
	int AdjGrpAddr, AdjListSize, NewNodeID, PtGrpKey, PtNumOnEdge;
	float EdgeDist, PtDist;
	set<int> todo;
	todo.clear();
	todo.insert(nodej);

	unordered_map<int, float> result;
	result.clear();
	set<int> visitedNode;
	visitedNode.clear();
	unordered_map<int, float> q;
	q.clear();
	for (int i = 0; i < se.size(); i++) {
		int id = se[i].node;
		float dis = se[i].dist;
		q[id] = dis;
	}

	// start
	int min, minpos, adjnode, weight;
	while (!todo.empty() && !q.empty()) {
		min = -1;
		for (unordered_map<int, float>::iterator it = q.begin(); it != q.end(); it++) {
			if (min == -1) {
				minpos = it->first;
				min = it->second;
			}
			else {
				if (it->second < min) {
					min = it->second;
					minpos = it->first;
				}
			}
		}
		//if (min > upperbound) break;
		// put min to result, add to visitedNode
		result[minpos] = min;
		visitedNode.insert(minpos);
		q.erase(minpos);

		if (todo.find(minpos) != todo.end()) {
			todo.erase(minpos);
		}

		// expand
		AdjGrpAddr = getAdjListGrpAddr(minpos);
		getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);

		for (int i = 0; i < AdjListSize; i++) {
			getVarE(ADJNODE_A, &adjnode, AdjGrpAddr, i);
			//adjnode = graph[minpos].adjnodes[i];
			if (visitedNode.find(adjnode) != visitedNode.end()) {
				continue;
			}

			getVarE(DIST_A, &weight, AdjGrpAddr, i);
			int iedist = (int)weight;
			weight = iedist;
			//weight = graph[minpos].adjweight[i];

			if (q.find(adjnode) != q.end()) {
				if (min + weight < q[adjnode]) {
					q[adjnode] = min + weight;
				}
			}
			else {
				q[adjnode] = min + weight;
			}

		}
	}

	// output
	float dis = INFINITE_MAX;
	if (result.count(nodej) > 0) {
		dis = result[nodej];
	}

	// return
	return dis;
}



void TA_EW(StepQueue* raQ, StepQueue& sQ) {
	float eKdist;
	int AdjListSize, NewNodeID, AdjGrpAddr, PtGrpKey;
	int PopSize = 0, VisitedSize = 0, NodeID;
	float cur_x, cur_y, nextdist;
	int curround, totround = 0;	// # of sorted access
	unsigned long long sumkwd;
	float lb_dist = 0;
	while (!sQ.empty()) {
		StepEvent event = sQ.top();
		sQ.pop();
		NodeID = event.node;
		//printf("The nodid is %d\n", NodeID);
		curround = event.ClusID;
		QueryPoint q = Q.querypts[curround];
		int teNi = q.Ni;
		int teNj = q.Nj;
		float dis = q.distEdge;
		float disn = q.dist_Ni;

		if (saVisited[curround][NodeID]) continue;
		saVisited[curround][NodeID] = true;	// !!!
											// ********new added
											//printf("The nodid is %d\n", NodeID);
		float di = event.dist;
		AdjGrpAddr = getAdjListGrpAddr(NodeID);
		getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);	// read # entries
		for (int z = 0; z<AdjListSize; z++) {
			getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, z);
			getVarE(DIST_A, Ref(eKdist), AdjGrpAddr, z);
			int iedist = (int)eKdist;
			eKdist = iedist;
			if (saVisited[curround][NewNodeID]) continue;
			int idist = (int)eKdist;
			eKdist = idist;
			// *** added part
			//getFixedF(XCRD_A, Ref(cur_x), AdjGrpAddr);
			//getFixedF(YCRD_A, Ref(cur_y), AdjGrpAddr);
			//StepEvent newevent = event;	// copy ...
			StepEvent newevent;
			newevent.node = NewNodeID;
			newevent.ClusID = event.ClusID;
			newevent.dist = event.dist + eKdist;
			// *** added part
			//newevent.xc = cur_x;
			//newevent.yc = cur_y;

			//if (saVisited[curround][NewNodeID] == false) sQ.push(newevent);	// propagation		
			sQ.push(newevent);	// propagation		
		}
		nextdist = event.dist;

		// get next of curround 
		DistMaps[curround][NodeID] = nextdist;	// assume valid result
												//raQ[curround].push(event);

		lb_dist = nextdist;

		float mindist = 0, curnetdist = 0;
		// *** added part
		//cur_x = event.xc;
		//cur_y = event.yc;

		for (int s = 0; s<Q.k; s++) {
			//float cpdist = getDist(cur_x, cur_y, M_xcrd[s], M_xcrd[s]);
			float cpdist = 0;
			if (DistMaps[s].count(NodeID)>0) cpdist = DistMaps[s][NodeID];

			//if (isWeightUse) cpdist = cpdist*weights[s];
			if (isSumDist) {
				mindist += lb_dist;
				curnetdist += cpdist;
			}
			else {
				mindist = max(mindist, lb_dist);
				curnetdist = max(curnetdist, cpdist);
			}
		}
		/*
		if (totround%PrintLimit == PrintLimit - 1) {
		printf("%d: %f %f\n", totround, mindist, bestdist);
		PrintElapsed();
		}
		*/
		totround++;
		// ***********逻辑上有问题？ 
		if (mindist >= rs.kthDist) break;

		bool mustPrune = true;
		for (int z = 0; z<AdjListSize; z++) {
			//getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, z);
			getVarE(DIST_A, Ref(eKdist), AdjGrpAddr, z);
			//getVarE(PTKEY_A, Ref(PtGrpKey), AdjGrpAddr, z);
			//getVarE(SUMKWD_A, Ref(sumkwd), AdjGrpAddr, z);
			//if ((sumkwd&Q.keywords) != Q.keywords) mustPrune = true;
			// L0^- filter
			int idist = (int)eKdist;
			eKdist = idist;
			if (isSumDist) {
				if (curnetdist<rs.kthDist + Q.k*eKdist) mustPrune = false;
				//break;
			}
			else {
				if (curnetdist<rs.kthDist + eKdist) mustPrune = false;
				//break;
			}
		}
		if (mustPrune) continue;

		//AdjGrpAddr = getAdjListGrpAddr(NodeID);
		//getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);	// read # entries
		for (int s = 0; s<Q.k; s++) {
			DISTMAP& curDistMap = DistMaps[s];
			if (curDistMap.count(NodeID) == 0) {
				//Repair_astar(raQ[s], raVisited[s], NodeID);
				A_star(raQ[s], raVisited[s], curDistMap, NodeID, PopSize, VisitedSize);
			}
		}
		for (int z = 0; z<AdjListSize; z++) {
			getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, z);
			getVarE(DIST_A, Ref(eKdist), AdjGrpAddr, z);
			int iedist = eKdist;
			eKdist = iedist;
			getVarE(PTKEY_A, Ref(PtGrpKey), AdjGrpAddr, z);
			getVarE(SUMKWD_A, Ref(sumkwd), AdjGrpAddr, z);
			nOfSEdgeExpended++;
			if ((sumkwd&Q.keywords) != Q.keywords) continue;
			// L0 filter
			if (isSumDist) {
				if (curnetdist >= rs.kthDist + Q.k*eKdist) continue;		// cannot have better distance
			}
			else {
				if (curnetdist >= rs.kthDist + eKdist) continue;		// cannot have better distance
			}

			// L1 filter
			if (getMinOptPos(NodeID, NewNodeID, eKdist) >= rs.kthDist) continue;
			if (PtGrpKey >= 0) {	// valid PtGrpKey  (-1 for invalid key)
				for (int s = 0; s<Q.k; s++) {
					DISTMAP& curDistMap = DistMaps[s];
					if (curDistMap.count(NewNodeID) == 0) {
						//Repair_astar(raQ[s], raVisited[s], NewNodeID);
						A_star(raQ[s], raVisited[s], curDistMap, NewNodeID, PopSize, VisitedSize);
					}
				}
				bool needUpdate = true;
				if (needUpdate) {
					float tmppossition;
					//float bestVal = 0;
					float bestVal = getOptPos(NodeID, NewNodeID, eKdist, tmppossition);
					if (bestVal >= rs.kthDist) needUpdate = false;
				}
				//UpdatePoints(NodeID, NewNodeID, PtGrpKey, eKdist);
				if (needUpdate) {
					//interkeyw = 
					UpdatePoints(NodeID, NewNodeID, PtGrpKey, eKdist);
				}
			}
		}
	}
	//printf("bestdist: %f\n", bestdist);
	//printf("totround: %d, pop size: %d, VisitedSize: %d\n", totround, PopSize, VisitedSize);

	/*rs.distance = INFINITE_MAX;
	rs.poid = -1;

	if (dQ_graph.begin() != dQ_graph.end()) {
	rs.distance = dQ_graph.begin()->dist;
	rs.poid = dQ_graph.begin()->id;
	}*/
	
	nOfPageAccessed = printPageAccess(-1);
	if (rs.topK.size() != rs.nOfAggPoint) cout << "Error in Top-k" << endl;
	int sumid = 0;
	for (int i = 0; i < rs.topK.size(); i++) {
		sumid = sumid + rs.topK[i].poid;
	}
	rs.sumpid = sumid;
	//printf("The result of TA distance is: %f\n", rs.kthDist);
	for (int l = 0; l < rs.topK.size(); l++) {
		cout << rs.topK[l].poid << " " << rs.topK[l].nodei << " " << rs.topK[l].nodej << " " << rs.topK[l].distance << endl;
	}
	

	printf("The TA sumid is: %d\n", rs.sumpid);
	//printf("The result of TA oid is: %d\n", rs.poid);
	//printf("The result of TA pageaccessed is: %I64d\n", nOfPageAccessed);
	//printf("The result of TA edgeexpand is: %d\n", nOfEdgeExpended);
	//printf("The result of TA edgeSexpand is: %I64d\n", nOfSEdgeExpended);
	//printf("The result of TA  nodei is: %d\n", rs.nodei);
	//printf("The result of TA  nodej is: %d\n", rs.nodej);
	//printf("The result of TA  kwdnode is: %llu\n", rs.kwdnode);
	//printf("The result of TA  interkew is: %llu\n", rs.inter);
	//printf("The result of TA  query is: %llu\n", Q.keywords);
}


inline void printSetting() {
	if (isNNquery) printf(",point"); else printf(",center");
	if (isSumDist) printf(",sum"); else printf(",max");
}


// Only find the necessary dist, not necessarily all pairs dist
void FindSoln(int curAlg) {	// "node" reused as the next nodeID instead !!!
	StepQueue sQ;
	StepEvent stepL, stepR;
	StepQueue *raQ, *saQ;
	//raQ = new StepQueue[Q.k];
	saQ = new StepQueue[Q.k];

	StepQueue *mtQ;
	mtQ = new StepQueue[Q.k];
	
	// initialization
	//bestdist = INFINITE_MAX;
	InitDQ(dQ_graph);	// clear kNN-dist heap

	onSameEdge.assign(Q.k, false);
	partdists = new float*[Q.k];
	for (int i = 0; i<Q.k; i++) partdists[i] = new float[2];
	compdist.assign(Q.k, MAX_DIST);
	bestcompdist.assign(Q.k, MAX_DIST);

	float vP, eDist, eKdist;
	int AdjListSize, Ni, Nj, NewNodeID, TmpAdjGrpAddr;

	while (!sQ.empty()) sQ.pop();
	for (int s = 0; s<Q.k; s++) {
		vP = Q.querypts[s].dist_Ni;
		Ni = Q.querypts[s].Ni;
		Nj = Q.querypts[s].Nj;

		// for greedy search and rapid elimination
		TmpAdjGrpAddr = getAdjListGrpAddr(Ni);
		//getFixedF(XCRD_A, Ref(x1), TmpAdjGrpAddr);
		//getFixedF(YCRD_A, Ref(y1), TmpAdjGrpAddr);

		// lookup eDist from adj. list. of Ni;
		getFixedF(SIZE_A, Ref(AdjListSize), TmpAdjGrpAddr);	// read # entries
		for (int z = 0; z<AdjListSize; z++) {
			getVarE(ADJNODE_A, Ref(NewNodeID), TmpAdjGrpAddr, z);
			getVarE(DIST_A, Ref(eKdist), TmpAdjGrpAddr, z);
			int iedist = eKdist;
			eKdist = iedist;
			if (NewNodeID == Nj) eDist = eKdist;
		}

		stepL.ClusID = stepR.ClusID = s;
		stepL.dist = vP;			stepL.node = Ni;
		stepR.dist = eDist - vP;	stepR.node = Nj;

		stepL.isSortAcc = true;	stepR.isSortAcc = true;	// ??? 4/3/2004 19:00
		sQ.push(stepL);			sQ.push(stepR);

		stepL.dist = vP;			stepL.hdist = 0;
		stepR.dist = eDist - vP;	stepR.hdist = 0;
		stepL.isSortAcc = false;	stepR.isSortAcc = false;	// ??? 4/3/2004 19:00
		mtQ[s].push(stepL);		mtQ[s].push(stepR);
	}


	for (int sp = 0; sp<Q.k; sp++)
		DistMaps[sp].clear(); // clear first (safe before use)


	saVisited = new BitStore[Q.k];
	raVisited = new BitStore[Q.k];
	for (int i = 0; i<Q.k; i++) {
		saVisited[i].assign(NodeNum, false);
		raVisited[i].assign(NodeNum, false);
	}

	if (curAlg == CE) {
		printf("\n[CE");
		printSetting();
		printf("]\n");
		ConcurrentExpansion(sQ);
		//RR_Expand(mtQ);
	}

	// later, change the ... for cache
	if (curAlg == TA) {
		printf("\n[TA");
		printSetting();
		printf("]\n");
		astar_Visits = new BitStore[Q.k];
		for (int i = 0; i<Q.k; i++)
			astar_Visits[i].assign(NodeNum, false);
		TA_EW(mtQ, sQ);
	}

	for (int loop = 0; loop < Q.k; loop++) {
		while (!mtQ[loop].empty()) mtQ[loop].pop();
		while (!saQ[loop].empty()) saQ[loop].pop();
		if (!saVisited[loop].empty()) vector<bool>().swap(saVisited[loop]);
		if (!raVisited[loop].empty()) vector<bool>().swap(raVisited[loop]);
		if (!astar_Visits[loop].empty()) vector<bool>().swap(astar_Visits[loop]);
	}
	//delete []raVisited;
	//delete []saVisited;
	//delete []astar_Visits;
	delete []mtQ;
	//delete []raQ;
	delete []saQ;
}

void getFiles(string path, set<string>& files)
{
	//文件句柄  
	long   hFile = 0;
	//文件信息  
	struct _finddata_t fileinfo;
	string p;
	if ((hFile = _findfirst(p.assign(path).append("\\*").c_str(), &fileinfo)) != -1)
	{
		do
		{
			//如果是目录,迭代之  
			//如果不是,加入列表  
			if ((fileinfo.attrib &  _A_SUBDIR))
			{
				if (strcmp(fileinfo.name, ".") != 0 && strcmp(fileinfo.name, "..") != 0)
					getFiles(p.assign(path).append("\\").append(fileinfo.name), files);
			}
			else
			{
				files.insert(p.assign(path));
			}
		} while (_findnext(hFile, &fileinfo) == 0);
		_findclose(hFile);
	}
}

void freeegstatu(edgeStatu& es) {
	vector<float>().swap(es.qTbdist);
}

void freepnode(pnode& pn) {
	int size = pn.bdist.size();
	vector<vector<float>>::iterator it = pn.bdist.begin();
	for (; it != pn.bdist.end(); it++) {
		vector<float> itr = *it;
		vector<float>().swap(itr);
	}
}

void releasememory() {
	if (algorithmId < 4) {
		// delete paID	
		map<int, PartAddr>::iterator it = paID.begin();
		//DISTMAP::iterator itr = elem_map.begin();
		for (; it != paID.end(); ) {
			it = paID.erase(it);
		}
		//printf("paID size is %d\n", paID.size());
		// delete EGT
		vector<TreeNode>::iterator ite = EGT.begin();
		for (; ite != EGT.end(); ) {
			TreeNode tn = *ite;
			freetreenode(tn);
			ite = EGT.erase(ite);
		}
		//printf("EGT size is %d\n", EGT.size());
		// delete visitedNode
		set<int>().swap(visitedNode);

		// delete edgevisited
		map<unsigned long long, edgeStatu>::iterator itev = edgevisited.begin();
		//DISTMAP::iterator itr = elem_map.begin();
		for (; itev != edgevisited.end(); ) {
			edgeStatu es = itev->second;
			freeegstatu(es);
			itev = edgevisited.erase(itev);
		}
		//printf("edgevisited size is %d\n", edgevisited.size());
		// free pq
		while (!pq.empty()) {
			pnode p = pq.top();
			freepnode(p);
			pq.pop();
		}
		//printf("pq size is %d\n", pq.size());
	}
	else if(algorithmId <6) {
		// delete elem_map
		if (elem_map.size()>0) {
			DISTMAP::iterator it = elem_map.begin();
			//DISTMAP::iterator itr = elem_map.begin();
			for (; it != elem_map.end(); ) {
				it = elem_map.erase(it);
			}
		}
		//printf("eleme_map size is %d\n", elem_map.size());
		// delete distmap
		for (int i = 0; i < Q.k; i++) {
			DISTMAP dis = DistMaps[i];
			DISTMAP::iterator it = dis.begin();
			//DISTMAP::iterator itr = elem_map.begin();
			for (; it != dis.end(); ) {
				it = dis.erase(it);
			}

		}
		//printf("dismap size is %d\n", elem_map.size());
		// delete dQ_graph
		if (dQ_graph.capacity() > 0) {
			vector<DistElem>().swap(dQ_graph);
			//dQ_graph.clear();
		}
		//printf("dQ_graph size is %d\n", dQ_graph.size());
	}
	else {
		// 释放Address
		map<int, int>().swap(addressM);
		addressM.clear();
		// 释放reAdjList
		map<int, map<int, float>> ::iterator itr = reAdjListM.begin();
		for (; itr != reAdjListM.end(); itr++) {
			map<int, float>().swap(itr->second);
			itr->second.clear();
		}
		map<int, map<int, float>>().swap(reAdjListM);
		reAdjListM.clear();
		// 释放reEdgeMap
		map<unsigned long long, vector<edgePoi>>::iterator ite = reEdgeMapM.begin();
		for (; ite != reEdgeMapM.end(); ite++) {
			vector<edgePoi>().swap(ite->second);
			ite->second.clear();
		}
		map<unsigned long long, vector<edgePoi>>().swap(reEdgeMapM);
		reEdgeMapM.clear();

		// 释放nvd
		map<int, vcell>::iterator itn = nvdM.begin();
		for (; itn != nvdM.end(); itn++) {
			// 释放neighborI
			set<int>().swap(itn->second.neighborI);
			itn->second.neighborI.clear();
			// 释放region
			vector<edgeSegment>().swap(itn->second.region);
			itn->second.region.clear();
			// 释放neighbor
			map<edgeSegment, vector<int>, Compare>::iterator itnb = itn->second.neighbor.begin();
			for (; itnb != itn->second.neighbor.end(); itnb++) {
				vector<int>().swap(itnb->second);
				itnb->second.clear();
			}
			map<edgeSegment, vector<int>, Compare>().swap(itn->second.neighbor);
			itn->second.neighbor.clear();

			// 释放borderTpoiborder
			map<edgeSegment, vector<float>, Compare>::iterator itnf = itn->second.borderTpoiborder.begin();
			for (; itnf != itn->second.borderTpoiborder.end(); itnf++) {
				vector<float>().swap(itnf->second);
				itnf->second.clear();
			}
			map<edgeSegment, vector<float>, Compare>().swap(itn->second.borderTpoiborder);
			itn->second.borderTpoiborder.clear();
		}
		map<int, vcell>().swap(nvdM);
		nvdM.clear();
	}

}

void queryAlgorithm(string fileprefix) {

	clock_t start1, start2, finish;
	if (algorithmId == EGTD) {
		OpenDiskComm(basepath, 200);
		//initialQuery(fileprefix);
		start1 = clock();
		initialQuery(fileprefix);
		start2 = clock();
		comQueryPath(Q, EGT);
		EGTDA();
		finish = clock();
		rs.time1 = (finish - start1);
		rs.time2 = (finish - start2);
		cout << "Time1 spend of EGTDA is:" << (finish - start1) << endl;
		cout << "Time2 spend of EGTDA is:" << (finish - start2) << endl << endl;
		releasememory();
		CloseDiskComm();
	}
	else if (algorithmId == EGETD) {
		//initialQuery(fileprefix);
		OpenDiskComm(basepath, 200);
		//initialQuery(fileprefix);
		start1 = clock();
		initialQuery(fileprefix);
		start2 = clock();
		comQueryPath(Q, EGT);
		EGETDA();
		finish = clock();
		rs.time1 = (finish - start1);
		rs.time2 = (finish - start2);
		cout << "Time1 spend of EGETDA is:" << (finish - start1) << endl;
		cout << "Time2 spend of EGETDA is:" << (finish - start2) << endl << endl;
		releasememory();
		CloseDiskComm();
	}
	if (algorithmId == EGANN) {
		//initialQuery(fileprefix);
		OpenDiskComm(basepath, 200);
		//initialQuery(fileprefix);
		start1 = clock();
		initialQuery(fileprefix);
		start2 = clock();
		//comQueryPath(Q, EGT);
		ANNEG();
		finish = clock();
		rs.time1 = (finish - start1);
		rs.time2 = (finish - start2);
		cout << "Time1 spend of EGANN is:" << (finish - start1) << endl;
		cout << "Time2 spend of EGANN is:" << (finish - start2) << endl << endl;
		releasememory();
		CloseDiskComm();
	}
	else if (algorithmId == TA) {
		//algorithmId = 2;
		OpenDiskComm(basepath, 200);
		//initialQuery(fileprefix);
		start1 = clock();
		initialQuery(fileprefix);
		start2 = clock();
		//comQueryPath(Q, EGT);
		if (isNNquery) NNnum = 1;	// force to find 1 center only !
		DistMaps = new DISTMAP[Q.k];
		RefreshCache();
		FindSoln(TA);
		finish = clock();
		rs.time1 = (finish - start1);
		rs.time2 = (finish - start2);
		//cout << "Time spend of EGETDA is:" << (finish - start) / CLOCKS_PER_SEC << endl;
		cout << "Time1 spend of TA is:" << (finish - start1) << endl;
		cout << "Time2 spend of TA is:" << (finish - start2) << endl << endl;
		releasememory();
		CloseDiskComm();
	}
	else if (algorithmId == CE) {
		//algorithmId = 2;
		OpenDiskComm(basepath, 200);
		//initialQuery(fileprefix);
		start1 = clock();
		initialQuery(fileprefix);
		start2 = clock();
		//comQueryPath(Q, EGT);
		if (isNNquery) NNnum = 1;	// force to find 1 center only !
		DistMaps = new DISTMAP[Q.k];
		RefreshCache();
		FindSoln(CE);
		finish = clock();
		rs.time1 = (finish - start1);
		rs.time2 = (finish - start2);
		//cout << "Time spend of EGETDA is:" << (finish - start) / CLOCKS_PER_SEC << endl;
		cout << "Time1 spend of CE is:" << (finish - start1) << endl;
		cout << "Time2 spend of CE is:" << (finish - start2) << endl << endl;
		releasememory();
		CloseDiskComm();
	}
	else if (algorithmId == NVD) {
		OpenDiskComm(basepath, 200);
		start1 = clock();
		initialQuery(fileprefix);
		start2 = clock();
		VANN();
		finish = clock();
		rs.time1 = (finish - start1);
		rs.time2 = (finish - start2);
		cout << "Time1 spend of VANN is:" << (finish - start1) << endl;
		cout << "Time2 spend of VANN is:" << (finish - start2) << endl << endl;
		releasememory();
		CloseDiskComm();
	}
}


int splitSegment(segmentTreeNode sc) {
	int median = -1, min = LONG_MAX, index = 0;
	if (sc.vStart >= sc.vEnd) return median;
	for (index = sc.vStart; index <= sc.vEnd; index++) {
		int leftPos = sc.vStart > 0 ? (sc.vStart - 1) : 0;
		int left, right;
		if (0 == leftPos) left = sumSpace[index].sumEmpty;
		else left = sumSpace[index].sumEmpty - sumSpace[leftPos].sumEmpty;
		leftPos = index;
		right = sumSpace[sc.vEnd].sumEmpty - sumSpace[leftPos].sumEmpty;
		if (left >= 0 && right >= 0) {
			int absMin = (int)fabs(left - right);
			if (absMin < min) {
				min = absMin;
				median = index;
			}
		}
	}
	return median;
}

struct modifiedInfo {
	int address;
	long long kwd;
};

clock_t startnow, endnow;
int times;
void updateDG(int lid, FILE *ptFile, FILE *alFile, string path) {

	cout << "Begin update: " << lid << endl;
	vector <int>::iterator iElement = find(leafNid.begin(), leafNid.end(), lid);
	if (iElement == leafNid.end()) {
		cout << " Error in updateDG!" << endl;
		return;
	}

	int pos = distance(leafNid.begin(), iElement);
	int startPOS, endPOS; //记录要更新的所有叶子节点，在LeafNid(叶子节点顺序存放)中的起始位置

	set<int> updateLeafID;
	updateLeafID.clear();
	updateLeafID.insert(lid);

	int totalEmpty=0;
	if (remainSpaceN[lid] >= 0) {
		startPOS = pos;
		endPOS = pos;
		totalEmpty = remainSpaceN[lid];
	}
	else { //我们采用广度优先策略找startPOS和endPOS	
		int itf = pos, itr = pos, isLeft = 1, leafID = 0;
		totalEmpty = remainSpaceN[lid];
		for (; itf < (leafNid.size() - 1) || itr > 0; ) {
			if (itf < (leafNid.size() - 1) && itr > 0) {
				if (isLeft) {//向左移:itr--
					itr--;
					leafID = leafNid[itr];
					totalEmpty = totalEmpty + remainSpaceN[leafID];
					isLeft = 0;
				}
				else {//itf++
					itf++;
					leafID = leafNid[itf];
					totalEmpty = totalEmpty + remainSpaceN[leafID];
					isLeft = 1;
				}
			}
			else if (itf < (leafNid.size() - 1)) {
				itf++;
				leafID = leafNid[itf];
				totalEmpty = totalEmpty + remainSpaceN[leafID];
			}
			else {
				itr--;
				leafID = leafNid[itr];
				totalEmpty = totalEmpty + remainSpaceN[leafID];
			}
			updateLeafID.insert(leafID);
			if (totalEmpty >= 0) break;
		}
		startPOS = itr > 0 ? itr : 0;
		endPOS = itf < leafNid.size() ? itf : (leafNid.size() - 1);
	}

	int nOfTotalEmpty = 0;
	sumSpace.clear();
	cout << "Begin update build remainSpace" << endl;
	// 找到了StartID和EndID的位置，读入Gtree中叶子节点信息，来构建emptySpace
	for (int m = startPOS; m <= endPOS; m++) {
		int leafID = leafNid[m];
		//vector<int> ::iterator it = EGT[leafID].leafnodes.begin();
		for (int n = 0; n < EGT[leafID].leafnodes.size(); n++) {
			int vid = EGT[leafID].leafnodes[n];
			// 看看该VID是否有更新操作，没有就跳过，有的话需要加入emptySpace;
			if (UTree[leafID].operations.find(vid) != UTree[leafID].operations.end()) {
				nOfEmpty ne;
				ne.vi = vid;
				nOfTotalEmpty = nOfTotalEmpty + remainSpaceV[vid];
				ne.sumEmpty = nOfTotalEmpty; // 每个vertex记录到该vertex为止的所有空位置的和
				sumSpace.push_back(ne);
			}
		}
	}

	cout << "Begin update build segmentTree." << endl;
	// 通过划分，构建线段树
	int threshold = 5; //用于停止线段树划分
	//int tempthre = totalEmpty / 64;
	//if (tempthre > threshold) threshold = tempthre;
	SegmentTree.clear();
	segmentTreeNode st;
	st.isLeaf = false;
	st.vStart = 0;
	st.vEnd = sumSpace.size() - 1;
	st.emptySize = sumSpace[st.vEnd].sumEmpty;
	if (totalEmpty != st.emptySize) {
		cout << "Empty Error !!!!!!!!!!!!!!!!!!!!!" << endl;
		return;
	}
	SegmentTree.push_back(st);
	int index = 0;
	while (true) {
		segmentTreeNode stCurrent = SegmentTree[index];
		if ((stCurrent.emptySize <= threshold) || (stCurrent.vStart >= stCurrent.vEnd)) { // 满足停止条件，不在划分
			stCurrent.isLeaf = true;
		}
		else {// 继续划分
			int median = splitSegment(stCurrent);
			if (median < 0) {
				stCurrent.isLeaf = true;				
			}
			else {
				// 构建两棵子树
				segmentTreeNode stLeft, stRight;
				int leftPos = stCurrent.vStart > 0 ? (stCurrent.vStart - 1) : 0;
				if (0 == leftPos) stLeft.emptySize = sumSpace[median].sumEmpty;
				else stLeft.emptySize = sumSpace[median].sumEmpty - sumSpace[leftPos].sumEmpty;
				stLeft.isLeaf = false;
				stLeft.vStart = stCurrent.vStart;
				stLeft.vEnd = median;
				st.pLeft = -1;
				st.pRight = -1;
				SegmentTree.push_back(stLeft);
				SegmentTree[index].pLeft = SegmentTree.size() - 1;

				//leftPos = median;
				//if (0 == leftPos) stRight.emptySize = sumSpace[stCurrent.vEnd].sumEmpty;
				stRight.emptySize = sumSpace[stCurrent.vEnd].sumEmpty - sumSpace[median].sumEmpty;
				stRight.isLeaf = false;
				stRight.vStart = median + 1;
				stRight.vEnd = stCurrent.vEnd;
				stRight.pLeft = -1;
				stRight.pRight = -1;
				SegmentTree.push_back(stRight);
				SegmentTree[index].pRight = SegmentTree.size() - 1;
				if ((stRight.emptySize + stLeft.emptySize) != stCurrent.emptySize) {
					cout << "构建SegmentTree Error !" << endl;
					return;
				}
			}
		}
		SegmentTree[index] = stCurrent;
		index++;
		cout << "index size is:" << index << " SegTree is: " << SegmentTree.size() << endl;
		if (index >= SegmentTree.size()) break;
		if (SegmentTree.size() >= 128) break;
	}
	for (int i = 0; i < SegmentTree.size(); i++) {
		if (SegmentTree[i].pLeft < 0 && SegmentTree[i].pRight < 0) SegmentTree[i].isLeaf = true;
	}

	cout << "Begin move to disk!" << endl;
	// 构建完线段树，然后按照线段树叶子节点的信息来移动外存
	// 修改EmptySpace
	for (int lp = 0; lp < SegmentTree.size(); lp++) {
		if (SegmentTree[lp].isLeaf) {
			// 获取分割的叶子线段在sumSpace中的起始位置，进一步获取他的ID
			int vSP = SegmentTree[lp].vStart;
			int vEP = SegmentTree[lp].vEnd;
			// 更新节点的emptySpace
			int sumEpty = 0, vid, nid;
			for (int ilp = vSP; ilp < vEP; ilp++) {
				vid = sumSpace[ilp].vi;
				nid = paID[vid].part;
				if (remainSpaceN.find(nid) == remainSpaceN.end()) remainSpaceN[nid] = 0;				
				remainSpaceN[nid] = remainSpaceN[nid] - remainSpaceV[vid];
				sumEpty += remainSpaceV[vid];
				remainSpaceV[vid] = 0;
			}

			vid = sumSpace[vEP].vi;
			nid = paID[vid].part;
			if (remainSpaceN.find(nid) == remainSpaceN.end()) remainSpaceN[nid] = 0;
			remainSpaceN[nid] = remainSpaceN[nid] + sumEpty;
			remainSpaceV[vid] = remainSpaceV[vid] + sumEpty;


			int vS = sumSpace[vSP].vi;
			int vE = sumSpace[vEP].vi;
			// 将vS，vE这段数据进行压缩（先保存到内存，然后再输出出去，最后将空白位置填充）
			int nodeidS = paID[vS].part;
			int nodeidE = paID[vE].part;
			int cnoid = -1;

			vector<int> ::iterator itv = find(leafNid.begin(), leafNid.end(), nodeidS);
			if (itv == leafNid.end()) {
				cout << " LeafNID Error !" << endl;
				return;
			}
			int posids = distance(leafNid.begin(), itv);
			int posidts = posids;
			itv = find(leafNid.begin(), leafNid.end(), nodeidE);
			if (itv == leafNid.end()) {
				cout << " LeafNID Error !" << endl;
				return;
			}
			int poside = distance(leafNid.begin(), itv);

			float vP, eDist, eKdist, PtDist;
			int startAddress;
			int AdjListSize, NewNodeID, AdjGrpAddr, PtGrpKey, PtNumOnEdge, RawAddr, key;

			map<int, map<int, vector<InerNode>>> waitModify;
			map<int, map<int, modifiedInfo>> address;

			bool isFirst = true;
			while (true) {
				// 对于每一个LeafNode,处理它里面所有的节点,直到遇到vE
				cnoid = leafNid[posidts];
				vector<int> vertexset = EGT[cnoid].leafnodes;
				vector<int> ::iterator itv = find(vertexset.begin(), vertexset.end(), vS);
				int pos = 0;
				if (itv != vertexset.end()) pos = distance(vertexset.begin(), itv);

				for (; pos < vertexset.size(); pos++) {
					int vid = vertexset[pos];

					if (waitModify.find(vid) == waitModify.end()) {
						map<int, vector<InerNode>> adjList;
						adjList.clear();
						waitModify[vid] = adjList;
					}

					AdjGrpAddr = paID[vid].addr;
					getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);
					if (AdjListSize < 0 || AdjListSize>100) {
						cout << "Error in AdjListSize File!" << endl;
						return;
					}

					for (int n = 0; n < AdjListSize; n++) {
						getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, n);
						getVarE(PTKEY_A, Ref(PtGrpKey), AdjGrpAddr, n);
						if (PTKEY_A == -1) continue;

						if (isFirst) {
							startAddress = PtGrpKey;
							isFirst = false;
						}

						if (waitModify[vid].find(NewNodeID) == waitModify[vid].end()) {
							vector<InerNode> nodeList;
							nodeList.clear();
							waitModify[vid][NewNodeID] = nodeList;
						}
						getFixedF(SIZE_P, Ref(PtNumOnEdge), PtGrpKey);
						if (PtNumOnEdge < 0 || PtNumOnEdge>100) {
							cout << "Error in AdjListSize Point File!" << endl;
							return;
						}
						int pid;
						unsigned long long pkwd;
						for (int j = 0; j < PtNumOnEdge; j++) {
							getVarE(PT_DIST, Ref(PtDist), PtGrpKey, j);
							getVarE(PT_KWD, &pkwd, PtGrpKey, j);
							getVarE(PT_P, &pid, PtGrpKey, j);
							InerNode in;
							in.dis = PtDist;
							in.pid = pid;
							in.vct = pkwd;
							waitModify[vid][NewNodeID].push_back(in);
						}
					}
					if (vid == vE) break;
				}

				// 批处理一个LeafNode中的已存在而不是所有的vertex的信息，插入和删除,即：修改waitModify
				map<int, vertexOperation> operationV = UTree[cnoid].operations;
				map<int, vertexOperation>::iterator itOpr = operationV.begin();
				for (; itOpr != operationV.end(); itOpr++) {
					int vid = itOpr->first;
					if (waitModify.find(vid) == waitModify.end()) continue; // 在waitModify中可能并不是保存所有的信息
					// 处理删除
					vector<operation> vop = itOpr->second.deleteV;
					for (int ld = 0; ld < vop.size(); ld++) {
						operation ope = vop[ld];
						int vdi = ope.vi;
						int vdj = ope.vj;
						int pid = ope.pid;
						vector<InerNode> inV;
						if (vid == vdi) inV = waitModify[vid][vdj];
						else inV = waitModify[vid][vdi];

						for (int l = 0; l < inV.size(); l++) {
							if (inV[l].pid == pid) {
								inV[l].dis = FLOAT_MAX;
								inV[l].pid = -1;
								inV[l].vct = 0;
								break;
							}
						}
						if (vid == vdi) waitModify[vid][vdj] = inV;
						else waitModify[vid][vdi] = inV;
					}

					// 处理加入
					vop = itOpr->second.insertV;
					for (int ld = 0; ld < vop.size(); ld++) {
						operation ope = vop[ld];
						int vdi = ope.vi;
						int vdj = ope.vj;

						vector<InerNode> inV;
						if (vid == vdi) inV = waitModify[vid][vdj];
						else inV = waitModify[vid][vdi];

						InerNode in;						
						in.dis = ope.dist;
						in.pid = ope.pid;
						in.vct = ope.kwd;

						int l;
						for (l = 0; l < inV.size(); l++) {
							if (inV[l].pid < 0) {
								inV[l] = in;
								break;
							}
						}
						if (l == inV.size()) inV.push_back(in);
						if (vid == vdi) waitModify[vid][vdj] = inV;
						else waitModify[vid][vdi] = inV;
					}
				}
				if (cnoid == nodeidE) break;	
				posidts++;
			}


			fseek(ptFile, startAddress, SEEK_SET);
			key = startAddress;
			// 对waitModify排序并写到外存,记录地址信息到address, 修改Point File
			map<int, map<int, vector<InerNode>>>::iterator itw = waitModify.begin();
			for (; itw != waitModify.end(); itw++) {
				int vid = itw->first;
				map<int, vector<InerNode>>::iterator itv = itw->second.begin();
				for (; itv != itw->second.end(); itv++) {
					int vjd = itv->first;
					vector<InerNode> inV = itv->second;
					sort(inV.begin(), inV.end(), CInerNode());
					unsigned long long sumkwd = 0;
					for (int l = 0; l < inV.size(); l++) {
						sumkwd |= inV[l].vct;
					}
					int pos = inV.size() - 1;
					// *******注意Pop_back的用法********
					while (true) {
						if (pos >= 0) {
							if (inV[pos].pid < 0) {
								inV.pop_back();
								pos--;								
							} 
							else break;
							
						}
						else break;
					}
					int PtSize = inV.size();
					eDist = 100;
					if (PtSize > 0) {
						//RawAddr = ftell(ptFile);	
						fwrite(&vid, 1, sizeof(int), ptFile);
						fwrite(&vjd, 1, sizeof(int), ptFile);
						fwrite(&eDist, 1, sizeof(float), ptFile);
						fwrite(&PtSize, 1, sizeof(int), ptFile);
						fwrite(&inV[0], inV.size(), sizeof(InerNode), ptFile);

						address[vid][vjd].address = key;
						address[vid][vjd].kwd = sumkwd;

						key += sizeof(int) * 3 + sizeof(float) + PtSize * sizeof(InerNode);
					}
					else {
						address[vid][vjd].address = -1; // also later used by AdjFile
						address[vid][vjd].kwd = 0;
					}
				}
			}

			// 最后修改Adjacency File
			posidts = posids;
			while (true) {
				// 对于每一个leafnode,处理它里面所有的节点
				cnoid = leafNid[posidts];
				vector<int> vertexset = EGT[cnoid].leafnodes;
				vector<int> ::iterator itv = find(vertexset.begin(), vertexset.end(), vS);
				int pos = 0;
				if (itv != vertexset.end()) pos = distance(vertexset.begin(), itv);

				for (; pos < vertexset.size(); pos++) {
					int vid = vertexset[pos];

					AdjGrpAddr = paID[vid].addr;
					getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);
					int ADJGRP_HEADSIZE = sizeof(int);
					int ADJGRP_ITEMSIZE = 2 * sizeof(int) + sizeof(float) + sizeof(unsigned long long);

					for (int n = 0; n < AdjListSize; n++) {
						getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, n);
						if (address.find(vid) == address.end()) {
							cout << "address Error !" << endl;
							return;
						}
						else {
							if (address[vid].find(NewNodeID) == address[vid].end()) {
								cout << "address Error !" << endl;
								return;
							}
						}
						int VarBaseA = AdjGrpAddr + ADJGRP_HEADSIZE + n*ADJGRP_ITEMSIZE;
						VarBaseA = VarBaseA + sizeof(int) + sizeof(float);
						fseek(alFile, VarBaseA, SEEK_SET);						
						unsigned long long kwd = address[vid][NewNodeID].kwd;
						int addss = address[vid][NewNodeID].address;
						fwrite(&kwd, 1, sizeof(unsigned long long), alFile);
						fwrite(&addss, 1, sizeof(int), alFile);
					}
					if (vid == vE) break;
				}

				if (cnoid == nodeidE) break;
				posidts++;
			}
		}
	}

	cout << "Begin update UTree." << endl;
	// 更新UTree节点，自下而上	
	for (int m = UTree.size() - 1; m >= 0; m--) {
		updateTreeNode utn = UTree[m];

		if (utn.isLeaf) {
			if (updateLeafID.find(m) == updateLeafID.end()) continue;
			utn.bitmap = 0;
			utn.nOfDelete = 0;
			utn.nOfInsert = 0;
			utn.nOfRemain = 0;
			utn.operations.clear();
			// 计算nOfRemain
			vector<int> leafNodes = EGT[m].leafnodes;
			for (int k = 0; k < leafNodes.size(); k++) {
				int vid = leafNodes[k];
				if (remainSpaceV.find(vid) != remainSpaceV.end()) {
					utn.nOfRemain += remainSpaceV[vid];
				}
			}
		}
		else {
			utn.bitmap = 0;
			utn.nOfDelete = 0;
			utn.nOfInsert = 0;
			utn.nOfRemain = 0;
			utn.operations.clear();
			vector<int> children = UTree[m].children;
			for (int il = 0; il < children.size(); il++) {
				int cid = children[il];
				utn.bitmap |= UTree[cid].bitmap;
				utn.nOfDelete += UTree[cid].nOfDelete;
				utn.nOfInsert += UTree[cid].nOfInsert;
				utn.nOfRemain += UTree[cid].nOfRemain;
			}
		}
	}
	nOfPageAccessed = printPageAccess(-1);
	times++;


	//if (0 == (times % 2)) {
	ofstream oFile(path.c_str(), ios::app);
	endnow = clock();
	oFile << wholeloop << "(" << times << "): " << (endnow - startnow) << " ; " << nOfPageAccessed << endl;
	if (0 == (times % 1000)) oFile << endl << endl << endl << endl << endl;
	
	oFile.close();
	//}	
}
	

int main(int argc, char *argv[]) {
	/*
	basepath = "..\\network\\ol";
	string datafilename = basepath;
	//cout << 1 << endl;
	//preprocessedge(datafilename);
	//maingendata(datafilename, rp);
	mainGenData(datafilename);
	printf("the end of generate nanp-data.\n");
	return 0;


	/*bitset<MAX_KEYWORDN> bit(167772160);
	cout << bit.count() << endl;
	return 0;*/

	/*basepath = "..\\network\\ol";
	OpenDiskComm(basepath, 200);
	geneQuery(basepath);
	CloseDiskComm();
	return 0;*/


	dataSetPath = "..\\network\\na";
	set<string> files;
	getFiles(dataSetPath, files);
	// construct the rtree index by traversing the subdir
	set<string>::iterator it = files.begin();
	int temp = 0;
	for (; it != files.end(); it++) {
		//temp++;
		//if (temp > 2) {
		//	//temp++;
		//	break;
		//}
		string pt = *it;
		basepath = pt;
		cout << basepath.c_str() << endl;
		//continue;
		// test whether query exist of qk&ts exists
		string queryFilename = basepath + "\\queryfile";
		fstream _file;
		_file.open(queryFilename, ios::in);
		if (!_file)
		{
			printf("%s Queryfile open error!\n", basepath);
		}
		else {
			string SUMResult = basepath + "\\SUMResult22";
			string MAXResult = basepath + "\\MAXResult22";
			// handle query
			ifstream iFile(queryFilename.c_str());
			ofstream oSFile(SUMResult.c_str());
			ofstream oMFile(MAXResult.c_str());
			int loop = 0;
			while (!iFile.eof()) {			
				string line;
				getline(iFile, line);
				if (line == "")
					continue;
				istringstream iss(line);

				char c;
				iss >> Q.keywords >> Q.k;
				Q.querypts.clear();

				queryedge.clear();
				for (int i = 0; i < Q.k; i++) {
					QueryPoint q;
					iss >> c >> q.Ni >> q.Nj >> q.distEdge >> q.dist_Ni;
					unsigned long long ni, nj;
					ni = q.Ni;
					nj = q.Nj;
					int idist = 0;
					q.distEdge = q.distEdge;
					idist = (int)q.distEdge;
					q.distEdge = idist;
					q.dist_Ni = q.dist_Ni;
					idist = (int)q.dist_Ni;
					q.dist_Ni = idist;
					//unsigned long long key = getKey(ni, nj);
					//queryedge.push_back(key);
					Q.querypts.push_back(q);
				}

				// start query
				int templ = (loop / 20) + 1;
				nOfAggregatePoint = 1;
				//nOfAggregatePoint = 1;
				cout << "***************Sum**************" << endl;
				isSumDist = true;
				for (int i = 1; i < 6; i++) {
					algorithmId = i;
					queryAlgorithm(basepath);
					oSFile << rs.sumpid<<" "<<nOfPageAccessed << " " << rs.time1 << " " << rs.time2 << ";";
				}
				oSFile << endl;
				//if (loop % 10 == 0) oSFile << endl << endl;
				cout << "***************Max**************" << endl;
				isSumDist = false;
				for (int i = 1; i <6; i++) {
					algorithmId = i;					
					queryAlgorithm(basepath);				
					oMFile << rs.sumpid << " " << nOfPageAccessed << " " << rs.time1 << " " << rs.time2 << ";";
				}
				loop++;
				oMFile << endl;


				//queryAlgorithm(dataFilename);
				if (loop % 20 == 0) {
					oSFile << endl << endl << endl << endl << endl;
					oMFile << endl << endl << endl << endl << endl;
				}

				printf("********Finish loop:%d******%s****\n", (loop), basepath.c_str());
				//break;
			}
			iFile.close();
			oSFile.close();
			oMFile.close();
			printf("----------------Finish Line-%s-----------------------\n", basepath);
		}
	}
	return 0;
}

//int main(int argc, char *argv[]) {
//	dataSetPath = "..\\na";
//	string path = "..\\na";
//	mainGenData(path);
//	//generateOperation(dataSetPath, 150000);
//	return 0;
//
//	//string path;
//	//set<string> files;
//	//getFiles(dataSetPath, files);
//	//// construct the rtree index by traversing the subdir
//	//set<string>::iterator it = files.begin();
//	//int temp = 0;
//	//for (; it != files.end(); it++) {
//	//	times = 0;
//	//	algorithmId = 1;
//	//	string pt = *it;
//	//	path = pt;
//	//	cout << path.c_str() << endl;
//	//	//continue;
//	//	OpenDiskComm(path, 200);
//	//	initialQuery(path);
//	//	// 从外存读取操作文件，构建Update tree
//	//	string operationFile = path + "\\operationFile";
//	//	string operationResult = path + "\\operationResult";
//
//	//	ifstream iFile(operationFile.c_str());
//	//	//ofstream oFile(operationResult.c_str());
//	//	wholeloop = 0;
//
//	//	clock_t start = clock();
//	//	startnow = clock();
//
//	//	while (!iFile.eof()) {
//	//		//if (times > 10008) break;
//	//		string line;
//	//		getline(iFile, line);
//	//		if (line == "") continue;
//	//		istringstream iss(line);
//	//		int isInsert, pid, vi, vj;
//	//		float dist;
//	//		unsigned long long word;
//	//		iss >> isInsert;
//	//		wholeloop++;
//	//		cout << wholeloop << endl;
//	//		if (isInsert) {
//	//			iss >> pid >> vi >> vj >> dist >> word;
//	//			operation opInsert;
//	//			opInsert.dist = dist;
//	//			opInsert.isDelete = false;
//	//			opInsert.kwd = word;
//	//			opInsert.pid = pid;
//	//			opInsert.vi = vi;
//	//			opInsert.vj = vj;
//	//			// 确定要插入的UTree Node
//	//			int nvi = paID[vi].part;
//	//			int nvj = paID[vj].part;
//	//			if (nvi == nvj) {
//	//				// 更新remainSpaceN, remainSpaceV
//	//				if (remainSpaceN.find(nvi) == remainSpaceN.end()) remainSpaceN[nvi] = 0;
//	//				remainSpaceN[nvi] = remainSpaceN[nvi] - 2;
//
//	//				if (remainSpaceV.find(vi) == remainSpaceV.end()) remainSpaceV[vi] = 0;
//	//				remainSpaceV[vi] = remainSpaceV[vi] - 1;
//	//				if (remainSpaceV.find(vj) == remainSpaceV.end()) remainSpaceV[vj] = 0;
//	//				remainSpaceV[vj] = remainSpaceV[vj] - 1;
//
//	//				UTree[nvi].bitmap |= opInsert.kwd;
//	//				UTree[nvi].nOfInsert = UTree[nvi].nOfInsert + 2;
//	//				UTree[nvi].nOfOperation = UTree[nvi].nOfOperation + 2;
//	//				if (UTree[nvi].operations.find(vi) != UTree[nvi].operations.end()) {
//	//					UTree[nvi].operations[vi].nOfI++;
//	//					UTree[nvi].operations[vi].insertV.push_back(opInsert);
//	//				}
//	//				else {
//	//					// 初始化
//	//					vector<operation> insertV;
//	//					insertV.clear();
//	//					vector<operation> deleteV;
//	//					deleteV.clear();
//	//					vertexOperation vo;
//
//	//					vo.nOfI = 0;
//	//					vo.nOfD = 0;
//	//					vo.deleteV = deleteV;
//	//					vo.insertV = insertV;
//
//	//					vo.nOfI++;
//	//					vo.insertV.push_back(opInsert);
//	//					UTree[nvi].operations[vi] = vo;
//	//				}
//
//
//	//				if (UTree[nvi].operations.find(vj) != UTree[nvi].operations.end()) {
//	//					UTree[nvi].operations[vj].nOfI++;
//	//					UTree[nvi].operations[vj].insertV.push_back(opInsert);
//	//				}
//	//				else {
//	//					// 初始化
//	//					vector<operation> insertV;
//	//					insertV.clear();
//	//					vector<operation> deleteV;
//	//					deleteV.clear();
//	//					vertexOperation vo;
//
//	//					vo.nOfI = 0;
//	//					vo.nOfD = 0;
//	//					vo.deleteV = deleteV;
//	//					vo.insertV = insertV;
//
//	//					vo.nOfI++;
//	//					vo.insertV.push_back(opInsert);
//	//					UTree[nvi].operations[vj] = vo;
//	//				}
//
//	//				if (UTree[nvi].nOfOperation > leafThre) {
//	//					updateDG(nvi, PtFile, AdjFile, operationResult);
//	//				}
//	//			}
//	//			else {
//	//				// 更新remainSpace, emptySpace
//	//				if (remainSpaceN.find(nvi) == remainSpaceN.end()) remainSpaceN[nvi] = 0;
//	//				remainSpaceN[nvi] = remainSpaceN[nvi] - 1;
//	//				if (remainSpaceN.find(nvj) == remainSpaceN.end()) remainSpaceN[nvj] = 0;
//	//				remainSpaceN[nvj] = remainSpaceN[nvj] - 1;
//
//	//				if (remainSpaceV.find(vi) == remainSpaceV.end()) remainSpaceV[vi] = 0;
//	//				remainSpaceV[vi] = remainSpaceV[vi] - 1;
//	//				if (remainSpaceV.find(vj) == remainSpaceV.end()) remainSpaceV[vj] = 0;
//	//				remainSpaceV[vj] = remainSpaceV[vj] - 1;
//
//
//
//	//				UTree[nvi].bitmap |= opInsert.kwd;
//	//				UTree[nvi].nOfInsert++;
//	//				UTree[nvi].nOfOperation++;
//	//				if (UTree[nvi].operations.find(vi) != UTree[nvi].operations.end()) {
//	//					UTree[nvi].operations[vi].nOfI++;
//	//					UTree[nvi].operations[vi].insertV.push_back(opInsert);
//	//				}
//	//				else {
//	//					// 初始化
//	//					vector<operation> insertV;
//	//					insertV.clear();
//	//					vector<operation> deleteV;
//	//					deleteV.clear();
//	//					vertexOperation vo;
//	//					vo.nOfI = 0;
//	//					vo.nOfD = 0;
//	//					vo.deleteV = deleteV;
//	//					vo.insertV = insertV;
//
//	//					vo.nOfI++;
//	//					vo.insertV.push_back(opInsert);
//	//					UTree[nvi].operations[vi] = vo;
//	//				}
//
//
//	//				UTree[nvj].bitmap |= opInsert.kwd;
//	//				UTree[nvj].nOfInsert++;
//	//				UTree[nvj].nOfOperation++;
//	//				if (UTree[nvj].operations.find(vj) != UTree[nvj].operations.end()) {
//	//					UTree[nvj].operations[vj].nOfI++;
//	//					UTree[nvj].operations[vj].insertV.push_back(opInsert);
//	//				}
//	//				else {
//	//					// 初始化
//	//					vector<operation> insertV;
//	//					insertV.clear();
//	//					vector<operation> deleteV;
//	//					deleteV.clear();
//	//					vertexOperation vo;
//	//					vo.nOfI = 0;
//	//					vo.nOfD = 0;
//	//					vo.deleteV = deleteV;
//	//					vo.insertV = insertV;
//
//	//					vo.nOfI++;
//	//					vo.insertV.push_back(opInsert);
//	//					UTree[nvj].operations[vj] = vo;
//	//				}
//
//	//				if (UTree[nvi].nOfOperation > leafThre) {
//	//					updateDG(nvi, PtFile, AdjFile, operationResult);
//	//				}
//
//	//				if (UTree[nvj].nOfOperation > leafThre) {
//	//					updateDG(nvj, PtFile, AdjFile, operationResult);
//	//				}
//	//			}
//	//		}
//	//		else {
//	//			iss >> pid >> vi >> vj;
//	//			operation opDelete;
//	//			opDelete.dist = 0;
//	//			opDelete.isDelete = true;
//	//			opDelete.kwd = 0;
//	//			opDelete.pid = pid;
//	//			opDelete.vi = vi;
//	//			opDelete.vj = vj;
//	//			// 确定要删除的UTree Node
//	//			int nvi = paID[vi].part;
//	//			int nvj = paID[vj].part;
//	//			if (nvi == nvj) {
//	//				// 更新remainSpace, emptySpace
//	//				if (remainSpaceN.find(nvi) == remainSpaceN.end()) remainSpaceN[nvi] = 0;
//	//				remainSpaceN[nvi] = remainSpaceN[nvi] + 2;
//
//	//				if (remainSpaceV.find(vi) == remainSpaceV.end()) remainSpaceV[vi] = 0;
//	//				remainSpaceV[vi] = remainSpaceV[vi] + 1;
//	//				if (remainSpaceV.find(vj) == remainSpaceV.end()) remainSpaceV[vj] = 0;
//	//				remainSpaceV[vj] = remainSpaceV[vj] + 1;
//
//
//	//				UTree[nvi].nOfDelete = UTree[nvi].nOfDelete + 2;
//	//				UTree[nvi].nOfOperation = UTree[nvi].nOfOperation + 2;
//	//				if (UTree[nvi].operations.find(vi) != UTree[nvi].operations.end()) {
//	//					UTree[nvi].operations[vi].nOfD++;
//	//					UTree[nvi].operations[vi].deleteV.push_back(opDelete);
//	//				}
//	//				else {
//	//					// 初始化
//	//					vector<operation> insertV;
//	//					insertV.clear();
//	//					vector<operation> deleteV;
//	//					deleteV.clear();
//	//					vertexOperation vo;
//	//					vo.nOfI = 0;
//	//					vo.nOfD = 0;
//	//					vo.deleteV = deleteV;
//	//					vo.insertV = insertV;
//
//	//					vo.nOfD++;
//	//					vo.deleteV.push_back(opDelete);
//	//					UTree[nvi].operations[vi] = vo;
//	//				}
//
//
//	//				if (UTree[nvi].operations.find(vj) != UTree[nvi].operations.end()) {
//	//					UTree[nvi].operations[vj].nOfD++;
//	//					UTree[nvi].operations[vj].deleteV.push_back(opDelete);
//	//				}
//	//				else {
//	//					// 初始化
//	//					vector<operation> insertV;
//	//					insertV.clear();
//	//					vector<operation> deleteV;
//	//					deleteV.clear();
//	//					vertexOperation vo;
//	//					vo.nOfI = 0;
//	//					vo.nOfD = 0;
//	//					vo.deleteV = deleteV;
//	//					vo.insertV = insertV;
//
//	//					vo.nOfD++;
//	//					vo.deleteV.push_back(opDelete);
//	//					UTree[nvi].operations[vj] = vo;
//	//				}
//
//	//				if (UTree[nvi].nOfOperation > leafThre) {
//	//					updateDG(nvi, PtFile, AdjFile, operationResult);
//	//				}
//	//			}
//	//			else {
//	//				// 更新remainSpace, emptySpace
//	//				if (remainSpaceN.find(nvi) == remainSpaceN.end()) remainSpaceN[nvi] = 0;
//	//				remainSpaceN[nvi] = remainSpaceN[nvi] + 1;
//	//				if (remainSpaceN.find(nvj) == remainSpaceN.end()) remainSpaceN[nvj] = 0;
//	//				remainSpaceN[nvj] = remainSpaceN[nvj] + 1;
//
//	//				if (remainSpaceV.find(vi) == remainSpaceV.end()) remainSpaceV[vi] = 0;
//	//				remainSpaceV[vi] = remainSpaceV[vi] + 1;
//	//				if (remainSpaceV.find(vj) == remainSpaceV.end()) remainSpaceV[vj] = 0;
//	//				remainSpaceV[vj] = remainSpaceV[vj] + 1;
//
//
//	//				UTree[nvi].nOfDelete++;
//	//				UTree[nvi].nOfOperation++;
//	//				if (UTree[nvi].operations.find(vi) != UTree[nvi].operations.end()) {
//	//					UTree[nvi].operations[vi].nOfD++;
//	//					UTree[nvi].operations[vi].deleteV.push_back(opDelete);
//	//				}
//	//				else {
//	//					// 初始化
//	//					vector<operation> insertV;
//	//					insertV.clear();
//	//					vector<operation> deleteV;
//	//					deleteV.clear();
//	//					vertexOperation vo;
//	//					vo.nOfI = 0;
//	//					vo.nOfD = 0;
//	//					vo.deleteV = deleteV;
//	//					vo.insertV = insertV;
//
//	//					vo.nOfD++;
//	//					vo.deleteV.push_back(opDelete);
//	//					UTree[nvi].operations[vi] = vo;
//	//				}
//
//
//	//				UTree[nvj].nOfDelete++;
//	//				UTree[nvj].nOfOperation++;
//	//				if (UTree[nvj].operations.find(vj) != UTree[nvj].operations.end()) {
//	//					UTree[nvj].operations[vj].nOfD++;
//	//					UTree[nvj].operations[vj].deleteV.push_back(opDelete);
//	//				}
//	//				else {
//	//					// 初始化
//	//					vector<operation> insertV;
//	//					insertV.clear();
//	//					vector<operation> deleteV;
//	//					deleteV.clear();
//	//					vertexOperation vo;
//	//					vo.nOfI = 0;
//	//					vo.nOfD = 0;
//	//					vo.deleteV = deleteV;
//	//					vo.insertV = insertV;
//
//	//					vo.nOfD++;
//	//					vo.deleteV.push_back(opDelete);
//	//					UTree[nvj].operations[vj] = vo;
//	//				}
//
//	//				if (UTree[nvi].nOfOperation > leafThre) {
//	//					updateDG(nvi, PtFile, AdjFile, operationResult);
//	//				}
//
//	//				if (UTree[nvj].nOfOperation > leafThre) {
//	//					updateDG(nvj, PtFile, AdjFile, operationResult);
//	//				}
//	//			}
//	//		}
//	//	}
//
//	//	clock_t end = clock();
//
//	//	nOfPageAccessed = printPageAccess(1);
//	//	ofstream oFile(operationResult.c_str(), ios::app);
//	//	end = clock();
//	//	oFile << endl << endl << "Final result(time/page):  " << (end - start) << " ; " << nOfPageAccessed << endl;		
//	//	oFile.close();
//
//	//	iFile.close();
//	//	CloseDiskComm();
//	//}
//	//return 0;
//}