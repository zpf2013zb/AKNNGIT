//#include "stdafx.h"
#include "utility.h"
#include "netshare.h"
#include "diskbased.h"
//#include "rtree.h"

#define min(a, b) (((a) < (b))? (a) : (b)  )
#define max(a, b) (((a) > (b))? (a) : (b)  )
#define ValAbs(x) (((x) >  0 )? (x) : -(x) )

typedef map<int, float> DISTMAP;
DISTMAP* DistMaps;	// only use cheap storage for range search
BitStore* astar_Visits;		// tmp. bitmap for A* search

BitStore *raVisited, *saVisited; // top-k
int PrintLimit;

typedef vector<int> 	IntVec;
typedef vector<float> 	FloatVec;

FloatVec M_xcrd, M_ycrd, compdist, bestcompdist;

BitStore onSameEdge;
float** partdists;
float bestdist;	// best value found so far

bool isNNquery = true;
bool isEuclidSpace = true;
bool isWeightUse = false;
char ptgrprtfn[255];

DistQueue dQ_graph;
extern BTree *PtTree;
extern struct QueryPoint;
//extern QueryPoint* Q.querypts;
extern int NodeNum;
extern int NNnum;
extern bool isSumDist;
//extern int Q.k;
extern Query Q;

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

// utilize the vj to update the distqueue
inline void UpdateOnePt(float vJ, bool& hasChanged, BitStore& onSameEdge, float eKdist, int ptid) {
	float dist = getNetworkDist(vJ, onSameEdge, eKdist);
	if (dist<bestdist) {	// for S-dist
		hasChanged = true;
		processDQ(dQ_graph, bestdist, dist, ptid);
		bestcompdist.assign(compdist.begin(), compdist.end());
	}
}

// 0 large 1 small // get a possible optimal position for in this edge
inline float getOptPos(int NodeID, int NewNodeID, float eKdist, float& bestPos) {
	float vJ, bestVal, tmpPos, tmpVal;
	int sid = 0, eid = 1;
	if (NewNodeID<NodeID) { sid = 1; eid = 0; }

	for (int sp = 0; sp<Q.k; sp++) {
		partdists[sp][0] = partdists[sp][1] = MAX_DIST;
		if (DistMaps[sp].count(NodeID)>0)
			partdists[sp][sid] = DistMaps[sp][NodeID];
		if (DistMaps[sp].count(NewNodeID)>0)
			partdists[sp][eid] = DistMaps[sp][NewNodeID];
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
	if (NewNodeID<NodeID) { sid = 1; eid = 0; }

	for (int sp = 0; sp<Q.k; sp++) {
		partdists[sp][0] = partdists[sp][1] = MAX_DIST;
		if (DistMaps[sp].count(NodeID)>0)
			partdists[sp][sid] = DistMaps[sp][NodeID];
		if (DistMaps[sp].count(NewNodeID)>0)
			partdists[sp][eid] = DistMaps[sp][NewNodeID];
		int qNi = Q.querypts[sp].Ni, qNj = Q.querypts[sp].Nj;
		onSameEdge[sp] = (NodeID == qNi&&NewNodeID == qNj) || (NodeID == qNj&&NewNodeID == qNi);
	}

	if (isNNquery) {
		int PtGrpSize, dummy;
		//PtGrpAddr = pointQuery(PtTree, PtGrpKey, dummy);

		getFixedF(SIZE_P, Ref(PtGrpSize), PtGrpAddr);
		for (int j = 0; j<PtGrpSize; j++) {	// scan
			int pid = 0;
			getVarE(PT_P, Ref(pid), PtGrpAddr, j);
			getVarE(PT_DIST, Ref(vJ), PtGrpAddr, j);
			getVarE(PT_KWD, Ref(sumkwd), PtGrpAddr, j);
			if ((sumkwd&Q.keywords) != Q.keywords) continue;
			UpdateOnePt(vJ, hasChanged, onSameEdge, eKdist, pid);
		}
	}
	else {
		vJ = 0;
		getOptPos(NodeID, NewNodeID, eKdist, vJ);
		UpdateOnePt(vJ, hasChanged, onSameEdge, eKdist, -1);
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
	int MaxHeapSize = 0, AggPopSize = 0;
	REGIONMAP epsNbrList;
	BitStore epsBits;
	int AdjListSize, NewNodeID, AdjGrpAddr, PtGrpKey;
	float eKdist, xVal, yVal;

	// initialize variables
	//if (!isEuclidSpace) return;
	epsBits.assign(NodeNum, false);
	int maxNbrSize = 0;
	while (!sQ.empty()) {
		if (MaxHeapSize<sQ.size()) MaxHeapSize = sQ.size();
		StepEvent event = sQ.top();
		sQ.pop();	AggPopSize++;

		int NodeID = event.node;
		int id = event.ClusID;

		if (DistMaps[id].count(NodeID)>0) continue;	// already found
		DistMaps[id][NodeID] = event.dist;

		float topbound = event.dist;	// change here !
		//if (isWeightUse) topbound = topbound*weights[id];
		if (topbound >= bestdist) continue;	// for both S-dist and M-dist: bound almost correct 

		AdjGrpAddr = getAdjListGrpAddr(NodeID);
		getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);	// read # entries
		//getFixedF(XCRD_A, Ref(xVal), AdjGrpAddr);
		//getFixedF(YCRD_A, Ref(yVal), AdjGrpAddr);

		maxNbrSize = max(maxNbrSize, epsNbrList.size());
		float epsilon = (isSumDist) ? (bestdist / Q.k) : (bestdist);
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
				if (curXdist >= bestdist) willErase = true;
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

		if (bestdist<MAX_DIST) {	// at least one found
			if (epsNbrList.size() == 0) break;	// all pruned => exit
		}

		for (int z = 0; z<AdjListSize; z++) {
			getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, z);
			getVarE(DIST_A, Ref(eKdist), AdjGrpAddr, z);
			// getVarE(DIST_A, Ref(eKdist), AdjGrpAddr, z);
			StepEvent newevent = event;	// copy ...
			newevent.node = NewNodeID;
			newevent.ClusID = event.ClusID;
			newevent.dist = event.dist + eKdist;
			if (DistMaps[id].count(NewNodeID) == 0) sQ.push(newevent);	// propagation

			// if error, add cond. to (... && not on same edge) [sp]
			bool needUpdate = true;
			for (int sp = 0; sp < Q.k; sp++) {
				if (DistMaps[sp].count(NodeID) == 0 || DistMaps[sp].count(NewNodeID) == 0) {
					needUpdate = false;
					break;
				}
					//needUpdate = false;
			}
				
			if (needUpdate&&isNNquery) {
				float tmpposition;
				float bestVal = getOptPos(NodeID, NewNodeID, eKdist, tmpposition);
				if (bestVal >= bestdist) needUpdate = false;
			}
			if (!needUpdate) continue;

			getVarE(PTKEY_A, Ref(PtGrpKey), AdjGrpAddr, z);
			if (PtGrpKey >= 0) {	// valid PtGrpKey  (-1 for invalid key)
				bool hasChanged = UpdatePoints(NodeID, NewNodeID, PtGrpKey, eKdist);
			}
		}
	}
	printf("Heap: max_size %d, pop_size %d\n", MaxHeapSize, AggPopSize);
	printf("bestdist: %f\n", bestdist);
	if (!sQ.empty()) printf("topdist: %f\n", sQ.top().dist);
	int totalmapsize = 0;
	for (int sp = 0; sp<Q.k; sp++) {
		//printf("%d) td_sz: %d\n",sp,DistMaps[sp].size());
		totalmapsize += DistMaps[sp].size();
	}
	printf("totalmapsize: %d, maxNbrSz: %d\n", totalmapsize, maxNbrSize);
}
// compute the distance between current node to the dest with the A* 
float A_star(StepQueue& aQ, BitStore& isVisited, DISTMAP& curdistmap,int dest, int& PopSize, int& VisitedSize) {
	// gdist: from src to cur ; hdist: from cur to dist
	float x_dest, y_dest, x_cur, y_cur;
	int TmpAdjGrpAddr = getAdjListGrpAddr(dest);
	//getFixedF(XCRD_A, Ref(x_dest), TmpAdjGrpAddr);
	//getFixedF(YCRD_A, Ref(y_dest), TmpAdjGrpAddr);

	while (!aQ.empty()) {
		StepEvent event = aQ.top();
		aQ.pop();	PopSize++;

		int NodeID = event.node;
		if (isVisited[NodeID]) continue;
		isVisited[NodeID] = true;		VisitedSize++;
		curdistmap[NodeID] = event.gdist;	// only gdist means the real dist. from src. !!!

		float eKdist;
		int AdjListSize, NewNodeID, AdjGrpAddr;
		AdjGrpAddr = getAdjListGrpAddr(NodeID);
		getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);	// read # entries
		for (int z = 0; z<AdjListSize; z++) {
			getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, z);
			getVarE(DIST_A, Ref(eKdist), AdjGrpAddr, z);

			StepEvent newevent = event;	// copy ...
			newevent.node = NewNodeID;
			newevent.gdist += eKdist;
			newevent.hdist = 0;

			TmpAdjGrpAddr = getAdjListGrpAddr(NewNodeID);
			//getFixedF(XCRD_A, Ref(x_cur), TmpAdjGrpAddr);
			//getFixedF(YCRD_A, Ref(y_cur), TmpAdjGrpAddr);
			newevent.xc = x_cur;		newevent.yc = y_cur;

			//if (isEuclidSpace) newevent.hdist = getDist(x_cur, y_cur, x_dest, y_dest);
			newevent.dist = newevent.gdist + newevent.hdist;

			// pathmax equation for non-monotonic heuristic ?
			if (newevent.dist<event.dist) newevent.dist = event.dist;
			if (isVisited[NewNodeID] == false) aQ.push(newevent);	// propagation		
		}
		if (NodeID == dest) return event.dist;
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
	StepEvent* tmpAry = new StepEvent[aQ.size()];

	float x_dest, y_dest, x_cur, y_cur;
	int TmpAdjGrpAddr = getAdjListGrpAddr(dest);
	//getFixedF(XCRD_A, Ref(x_dest), TmpAdjGrpAddr);
	//getFixedF(YCRD_A, Ref(y_dest), TmpAdjGrpAddr);

	while (!aQ.empty()) {
		StepEvent event = aQ.top();
		aQ.pop();
		if (isVisited[event.node]) continue;

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
		curround = event.ClusID;
		if (saVisited[curround][NodeID]) continue;
		saVisited[curround][NodeID] = true;	// !!!

		AdjGrpAddr = getAdjListGrpAddr(NodeID);
		getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);	// read # entries
		for (int z = 0; z<AdjListSize; z++) {
			getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, z);
			getVarE(DIST_A, Ref(eKdist), AdjGrpAddr, z);
			// *** added part
			//getFixedF(XCRD_A, Ref(cur_x), AdjGrpAddr);
			//getFixedF(YCRD_A, Ref(cur_y), AdjGrpAddr);
			StepEvent newevent = event;	// copy ...
			newevent.node = NewNodeID;
			newevent.dist = event.dist + eKdist;
			// *** added part
			//newevent.xc = cur_x;
			//newevent.yc = cur_y;

			if (saVisited[curround][NewNodeID] == false) sQ.push(newevent);	// propagation		
		}
		nextdist = event.dist;

		// get next of curround 
		DistMaps[curround][NodeID] = nextdist;	// assume valid result
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
		if (totround%PrintLimit == PrintLimit - 1) {
			printf("%d: %f %f\n", totround, mindist, bestdist);
			PrintElapsed();
		}
		totround++;
		if (mindist >= bestdist) break;

		bool mustPrune = true;
		for (int z = 0; z<AdjListSize; z++) {
			getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, z);
			getVarE(DIST_A, Ref(eKdist), AdjGrpAddr, z);
			getVarE(PTKEY_A, Ref(PtGrpKey), AdjGrpAddr, z);
			getVarE(SUMKWD_A, Ref(sumkwd), AdjGrpAddr, z);
			//if ((sumkwd&Q.keywords) != Q.keywords) mustPrune = true;
			// L0^- filter
			if (isSumDist) {
				if (curnetdist<bestdist + Q.k*eKdist) mustPrune = false;
				break;
			}
			else {
				if (curnetdist<bestdist + eKdist) mustPrune = false;
				break;
			}
		}
		if (mustPrune) continue;

		AdjGrpAddr = getAdjListGrpAddr(NodeID);
		getFixedF(SIZE_A, Ref(AdjListSize), AdjGrpAddr);	// read # entries
		for (int s = 0; s<Q.k; s++) {
			DISTMAP& curDistMap = DistMaps[s];
			if (curDistMap.count(NodeID) == 0) {
				Repair_astar(raQ[s], raVisited[s], NodeID);
				A_star(raQ[s], raVisited[s], curDistMap, NodeID, PopSize, VisitedSize);
			}
		}
		for (int z = 0; z<AdjListSize; z++) {
			getVarE(ADJNODE_A, Ref(NewNodeID), AdjGrpAddr, z);
			getVarE(DIST_A, Ref(eKdist), AdjGrpAddr, z);
			getVarE(PTKEY_A, Ref(PtGrpKey), AdjGrpAddr, z);
			getVarE(SUMKWD_A, Ref(sumkwd), AdjGrpAddr, z);
			if ((sumkwd&Q.keywords) != Q.keywords) continue;
			// L0 filter
			if (isSumDist) {
				if (curnetdist >= bestdist + Q.k*eKdist) continue;		// cannot have better distance
			}
			else {
				if (curnetdist >= bestdist + eKdist) continue;		// cannot have better distance
			}

			// L1 filter
			if (getMinOptPos(NodeID, NewNodeID, eKdist) >= bestdist) continue;
			if (PtGrpKey >= 0) {	// valid PtGrpKey  (-1 for invalid key)
				for (int s = 0; s<Q.k; s++) {
					DISTMAP& curDistMap = DistMaps[s];
					if (curDistMap.count(NewNodeID) == 0) {
						Repair_astar(raQ[s], raVisited[s], NewNodeID);
						A_star(raQ[s], raVisited[s], curDistMap, NewNodeID, PopSize, VisitedSize);
					}
				}
				bool needUpdate = true;
				if (needUpdate) {
					float tmppossition;
					float bestVal = getOptPos(NodeID, NewNodeID, eKdist, tmppossition);
					if (bestVal >= bestdist) needUpdate = false;
				}
				if (needUpdate) UpdatePoints(NodeID, NewNodeID, PtGrpKey, eKdist);
			}
		}
	}
	printf("bestdist: %f\n", bestdist);
	printf("totround: %d, pop size: %d, VisitedSize: %d\n", totround, PopSize, VisitedSize);
}


inline void printSetting() {
	if (isNNquery) printf(",point"); else printf(",center");
	if (isSumDist) printf(",sum"); else printf(",max");
}

enum ALGTYPE { Alg_CE, Alg_TA, Alg_TA_EW };
int algorithmId;
int getAdjListGrpAddr(int NodeID)  	// using AdjFile
{
	int addr = sizeof(int) + NodeID*sizeof(int), GrpAddr;
	char* BlockAddr = getFlatBlock(AdjFile, addr / BlkLen);
	memcpy(Ref(GrpAddr), BlockAddr + (addr%BlkLen), sizeof(int));
	addr = GrpAddr;
	return addr;
}

// Only find the necessary dist, not necessarily all pairs dist
void FindSoln(ALGTYPE curAlg) {	// "node" reused as the next nodeID instead !!!
	StepQueue sQ;
	StepEvent stepL, stepR;
	StepQueue *raQ, *saQ;
	raQ = new StepQueue[Q.k];
	saQ = new StepQueue[Q.k];
	
	StepQueue *mtQ;
	mtQ = new StepQueue[Q.k];

	// initialization
	bestdist = MAX_DIST;
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
			if (NewNodeID == Nj) eDist = eKdist;
		}

		stepL.ClusID = stepR.ClusID = s;
		stepL.dist = vP;			stepL.node = Ni;
		stepR.dist = eDist - vP;	stepR.node = Nj;

		stepL.isSortAcc = true;	stepR.isSortAcc = true;	// ??? 4/3/2004 19:00
		sQ.push(stepL);			sQ.push(stepR);

		stepL.gdist = vP;			stepL.hdist = 0;
		stepR.gdist = eDist - vP;	stepR.hdist = 0;
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

	if (curAlg == Alg_CE) {
		printf("\n[CE");
		printSetting();
		printf("]\n");
		ConcurrentExpansion(sQ);
		//RR_Expand(mtQ);
	}

	// later, change the ... for cache
	if (curAlg == Alg_TA) {
		printf("\n[TA");
		printSetting();
		printf("]\n");
		astar_Visits = new BitStore[Q.k];
		for (int i = 0; i<Q.k; i++)
			astar_Visits[i].assign(NodeNum, false);
		TA_EW(raQ, sQ);
	}
}

// error for 10000 times: 2.804688

int main(int argc, char** argv) {

	if (!isNNquery) NNnum = 1;	// force to find 1 center only !
	DistMaps = new DISTMAP[Q.k];

	RefreshCache();
	FindSoln(Alg_CE);

	// FindSoln(Alg_TA);
	return 0;
}
