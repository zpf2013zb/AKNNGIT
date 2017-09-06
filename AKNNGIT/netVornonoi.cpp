
#include "netVornonoi.h"
#include <iostream>
#include <set>
#include <unordered_set>
#include <unordered_map>
#include <sstream>
using namespace std;

extern int NodeNum;
extern int poiNodeNum;

map<int, map<int, float>> reAdjList; //重构后的路网的相邻链表
map<int, vcell> nvd;
map<int, int> address;
map<unsigned long long, vector<edgePoi>> reEdgeMap;


//struct com
//{
//	bool operator () (const label& left, const label& right) const
//	{
//		return left.minDist > right.minDist;
//	}
//};

// 注意这里有一个判断border是否相等的测试，他是float
bool isEqual(edgeSegment es1, edgeSegment es2) {
	if ((es1.ni == es2.ni) && (es1.nj == es2.nj) && (es1.border == es2.border)) return true;
	else return false;
}

unordered_map<int, float> dijkstraBorder(int start, float disstart, int end, float disend, vector<int> cands) {
	//int AdjGrpAddr, AdjListSize, NewNodeID, PtGrpKey, PtNumOnEdge;
	//float EdgeDist, PtDist;

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

		map<int, float> nb = reAdjList[minpos];
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
		output[cands[i]]= result[cands[i]];
	}

	// return
	return output;
}

void computeBorder() {
	//注意：POI的id是从NodeNum开始的
	//cout << "Start computeBorder" << endl;
	for (int i = NodeNum; i < poiNodeNum; i++) {
		//cout << "computeBorder id is: " << i << endl;
		vector<edgeSegment> rg1 = nvd[i].region;
		int rsize = rg1.size();

		set<int> visitedNode;
		visitedNode.clear();
		map<int, float> q;
		q[i] = 0;
		// start
		int minpos, adjnode;
		float min, weight;
		set<int> target; 
		vector<int> targetv;
		// 初始将generator压入到这里
		target.insert(i);
		targetv.push_back(i);
		while (!q.empty()) {
			min = INFINITY;
			for (map<int, float>::iterator it = q.begin(); it != q.end(); it++) {
				if (it->second < min) {
					minpos = it->first;
					min = it->second;
				}
			}
			// put min to result, add to visitedNode			
			visitedNode.insert(minpos);
			q.erase(minpos);
			// 如果是poi那么停止查询，直接判断是否有共同交点
			if ((minpos >= NodeNum) && (minpos != i)) {
				vector<edgeSegment> rg2 = nvd[minpos].region;
				for (int m = 0; m < rg1.size(); m++) {
					edgeSegment es1 = rg1[m];
					for (int n = 0; n < rg2.size(); n++) {
						edgeSegment es2 = rg2[n];
						if (isEqual(es1, es2)) {
							if (nvd[i].neighborI.find(minpos) == nvd[i].neighborI.end()) {
								nvd[i].neighborI.insert(minpos);
							}
								
							edgeSegment es = es1;
							if (target.find(es.ni) == target.end()) {
								target.insert(es.ni);
								targetv.push_back(es.ni);
							}
							if (target.find(es.nj) == target.end()) {
								target.insert(es.nj);
								targetv.push_back(es.nj);
							}
							// 注意这里！！！是找es
							if (nvd[i].neighbor.find(es) == nvd[i].neighbor.end()) {
								vector<int> nb;
								nb.push_back(minpos);
								nvd[i].neighbor[es] = nb;
							}
							else {
								nvd[i].neighbor[es].push_back(minpos);
							}
						}
					}
				}
				continue;
			}

			map<int, float> adj = reAdjList[minpos];
			map<int, float> ::iterator itadj = adj.begin();

			for (; itadj != adj.end(); itadj++) {
				int nid = itadj->first;
				weight = itadj->second;
				if (visitedNode.find(nid) != visitedNode.end()) continue;
				if (q.find(nid) != q.end()) {
					if (min + weight < q[nid]) {
						q[nid] = min + weight;
					}
				}
				else q[nid] = min + weight;				
			}
		}
		//cout << "Finish compute all neighbor" << endl;


		// 计算border到border的距离以及到generator的距离
		map<edgeSegment, vector<int>, Compare> bdmap = nvd[i].neighbor;
		map<edgeSegment, vector<int>, Compare> ::iterator itbdmap = nvd[i].neighbor.begin();
		//cout << "total num of neighbor is: " <<i<<"    "<<bdmap.size() << endl;
		for (; itbdmap != nvd[i].neighbor.end(); itbdmap++) {
			edgeSegment es = itbdmap->first;
			int sid = es.ni;
			float sdis = es.border;
			int eid = es.nj;
			float edis = reAdjList[sid][eid] - es.border;
			//cout << "The neighbor is " <<sid<<" " <<eid<< endl;
			unordered_map<int, float> result = dijkstraBorder(sid, sdis, eid, edis, targetv);
			//cout << "Finish dijkstraBorder" << endl;
			// 接下来计算当前border到所有其他border的距离
			vector<float> bTpoibddist;
			map<edgeSegment, vector<int>, Compare> ::iterator itbdmap2 = nvd[i].neighbor.begin();
			for (; itbdmap2 != nvd[i].neighbor.end(); itbdmap2++) {
				edgeSegment es2 = itbdmap2->first;
				if (isEqual(es, es2)) {
					bTpoibddist.push_back(0);
					continue;
				} 
				if ((es.ni == es2.ni) && (es.nj == es2.nj)) {
					cout << "Multiple borders on the same edge!!!" << endl;
				}
				int ni, nj;
				ni = es2.ni;
				nj = es2.nj;
				float disti = result[ni] + es2.border;
				float distj = result[nj] + reAdjList[ni][nj] - es2.border;
				if (disti < distj) distj = disti;
				bTpoibddist.push_back(distj);
			}
			//cout << "Finish bTbdist computation" << endl;
			bTpoibddist.push_back(result[i]);
			nvd[i].borderTpoiborder[es] = bTpoibddist;
		}
	}
}

// 有三个任务：1）构建POI和Vertex的路网相邻链表；2）划分路网； 3） 根据新的路网来计算border和距离
void buildNVD(EdgeMapType EdgeMap) {
	//cout << "Start BuildNVD" << endl;
	int ni, nj, pid;
	float dist;
	map<int, unsigned long long> poiTkwd; //保存POI到keyword的映射
	//cout << "EdgeSize is: " << EdgeMap.size() << endl;
	EdgeMapType::iterator iter = EdgeMap.begin();
	int lp = 0;
	for (; iter != EdgeMap.end(); iter++) {
		//cout << "EdgeNum is: " << EdgeMap.size() << "   " << lp++ << endl;
		unsigned long long key = iter->first;
		edge* e = iter->second;	
		ni = e->Ni;
		nj = e->Nj;
		dist = e->dist;
		vector<InerNode> pois = e->pts;
		// 和前面的节点进行互动
		vector<edgePoi> edgeReserve;
		// 这个时候的POIs是按照到ni的距离有小到大排列的
		for (int i = 0; i < pois.size(); i++) {
			//cout << "The number of i is: " << i << endl;
			pid = pois[i].pid + NodeNum;
			poiTkwd[pid] = pois[i].vct;
			edgePoi ep;
			ep.pid = pid;
			ep.dist = pois[i].dis;
			edgeReserve.push_back(ep);
			if (0 == i) {
				if (reAdjList.find(ni) == reAdjList.end()) {
					map<int, float> adj;
					adj[pid] = pois[i].dis;
					reAdjList[ni] = adj;
				}
				else {
					reAdjList[ni][pid] = pois[i].dis;
				}
				map<int, float> adjP;
				adjP[ni] = pois[i].dis;
				reAdjList[pid] = adjP;
			}
			else {
				int prepid = pois[i-1].pid + NodeNum;
				if (reAdjList.find(prepid) == reAdjList.end()) {
					map<int, float> adj;
					adj[pid] = pois[i].dis - pois[i-1].dis;
					reAdjList[prepid] = adj;
					cout << "Error in netVoronoi build1!" << endl;
				}
				else {
					reAdjList[prepid][pid] = pois[i].dis - pois[i-1].dis;
				}
				map<int, float> adjP;
				adjP[prepid] = pois[i].dis - pois[i-1].dis;
				if (adjP[prepid] < 0) cout << "Error in netVoronoi build2!" << endl;
				reAdjList[pid] = adjP;
			}
		}

		reEdgeMap[key] = edgeReserve;
		// 处理最后一个元素
		int pos = pois.size() - 1;
		pid = pois[pos].pid + NodeNum; //???
		if (reAdjList.find(pid) == reAdjList.end()) {
			cout << "Error in reAdjList build" << endl;
		}
		reAdjList[pid][nj] = dist - pois[pos].dis;
		// 处理nj
		if (reAdjList.find(nj) == reAdjList.end()) {
			map<int, float> adj;
			adj[pid] = dist - pois[pos].dis;
			reAdjList[nj] = adj;
		}
		else {
			reAdjList[nj][pid] = dist - pois[pos].dis;
		}		
	}

	//cout << "Finish BuildNVD reAdjList" << endl;
	// 开始准备路网划分
	map<int, label> mapSetT; //临时使用
	map<int, label> mapSetP; //最终结果
	//priority_queue<label, vector<label>, com> labelPQ;	
	// 初始化label
	for (int i = 0; i < poiNodeNum; i++) {
		label lb;
		set<int> minS;
		minS.clear();
		lb.minSet = minS;
		if (i < NodeNum) lb.minDist = INFINITY - 1;		
		else {
			lb.minDist = 0;
			lb.minSet.insert(i);
		}
		mapSetT[i] = lb;
	}
	cout << mapSetT.size() << endl;
	while (mapSetT.size()) {
		//cout << "loop MapSetT.size() is :" << mapSetT.size() << endl;
		map<int, label> ::iterator it = mapSetT.begin();
		float minD = INFINITY;
		int minI = -1;
		for (; it != mapSetT.end(); it++) {
			label lb = it->second;
			if (-1 == minI) {
				minI = it->first;
				minD = lb.minDist;
			}
			else {
				if (lb.minDist <  minD) {
					minI = it->first;
					minD = lb.minDist;
				}
			}
		}

		mapSetP[minI] = mapSetT[minI];
		// 更新minI的邻居
		map<int, float> nb = reAdjList[minI];
		map<int, float> ::iterator itn = nb.begin();
		for (; itn != nb.end(); itn++) {
			int nid = itn->first;
			float dist = itn->second;
			dist = dist + mapSetT[minI].minDist;
			if (mapSetT.find(nid) != mapSetT.end()) {//这个判断很重要
				if (dist < mapSetT[nid].minDist) {
					mapSetT[nid].minDist = dist;
					mapSetT[nid].minSet = mapSetT[minI].minSet;
				}
				else if (dist == mapSetT[nid].minDist) {//这个还是要考虑的，float比较
					set<int> ::iterator itset = mapSetT[minI].minSet.begin();
					for (; itset != mapSetT[minI].minSet.end(); itset++) {
						int sid = *itset;
						if (mapSetT[nid].minSet.find(sid) == mapSetT[nid].minSet.end()) {
							mapSetT[nid].minSet.insert(sid);
						}
					}
				}
			}
		}
		mapSetT.erase(minI);
	}

	//cout << "Finish BuildNVD Label" << endl;
	// 开始划分 voronoi partition
	nvd.clear();
	set<unsigned long long> visited;
	map<int, map<int, float>> ::iterator iti = reAdjList.begin();
	for (; iti != reAdjList.end(); iti++) {
		int ni = iti->first;
		map<int, float> ::iterator itj = iti->second.begin();
		for (; itj != iti->second.end(); itj++) {
			int nj = itj->first;
			unsigned long long key = getKey(ni, nj);
			if (key < 0 || ni < 0 || nj < 0) {
				cout << "Key Error in netVoronoi" << endl;
			}
			if (visited.find(key) != visited.end()) continue;
			visited.insert(key);
			int Ni = ni < nj ? ni : nj;
			int Nj = ni > nj ? ni : nj;
			set<int> xi = mapSetP[ni].minSet;
			set<int> xj = mapSetP[nj].minSet;

			set<int> ::iterator itxi = xi.begin();
			for (; itxi != xi.end(); itxi++) {
				int xie = *itxi;
				if (nvd.find(xie) == nvd.end()) {
					vcell vc;
					vc.kwd = poiTkwd[xie];
					vc.pid = xie;
					
					map<edgeSegment, vector<float>, Compare> bTp;
					bTp.clear();
					vc.borderTpoiborder = bTp;

					map<edgeSegment, vector<int>, Compare> nb;
					nb.clear();
					vc.neighbor = nb;

					vector<edgeSegment> rg;
					rg.clear();
					vc.region = rg;		
					nvd[xie] = vc;
				}

				edgeSegment es;
				es.ni = Ni;
				es.nj = Nj;
				if (xj.find(xie) != xj.end()) { //属于交集
					es.start = 0;
					es.end = reAdjList[ni][nj];
					if(ni<nj) es.border = es.end;
					else es.border = es.start;
				}
				else {
					float pos = 0.5 * (mapSetP[nj].minDist - mapSetP[ni].minDist + reAdjList[ni][nj]);
					if (ni < nj) {
						es.start = 0;
						es.end = pos;
						es.border = es.end;
					}
					else {
						es.start = reAdjList[ni][nj] - pos;
						es.end = reAdjList[ni][nj];
						es.border = es.start;
					}
				}
				nvd[xie].region.push_back(es);
			}

			itxi = xj.begin();
			for (; itxi != xj.end(); itxi++) {
				int xie = *itxi;
				if (nvd.find(xie) == nvd.end()) {
					vcell vc;
					vc.kwd = poiTkwd[xie];
					vc.pid = xie;

					map<edgeSegment, vector<float>, Compare> bTp;
					bTp.clear();
					vc.borderTpoiborder = bTp;

					map<edgeSegment, vector<int>, Compare> nb;
					nb.clear();
					vc.neighbor = nb;

					vector<edgeSegment> rg;
					rg.clear();
					vc.region = rg;

					nvd[xie] = vc;
				}			
				if (xi.find(xie) == xi.end()) {
					edgeSegment es;
					es.ni = Ni;
					es.nj = Nj;
					float pos = 0.5 * (mapSetP[ni].minDist - mapSetP[nj].minDist + reAdjList[ni][nj]);
					if (ni > nj) {
						es.start = 0;
						es.end = pos;
						es.border = es.end;
					}
					else {
						es.start = reAdjList[ni][nj] - pos;
						es.end = reAdjList[ni][nj];
						es.border = es.start;
					}
					nvd[xie].region.push_back(es);
				}
			}

		}
	}
	//cout << "Finish BuildNVD partition" << endl;
	// 接下来要利用reAdjList来遍历每个POI来获取他们的边界，注意目前保存在region中的edgesegment未必是边界，需要进一步确定,下面函数用于计算border和距离
	computeBorder();
	cout << "Finish BuildNVD computeBorder" << endl;
}

void saveNVD(string filename) {
	cout << "start saveNVD" << endl;
	string pathnvd = filename + "\\nvd";
	FILE *fout = fopen(pathnvd.c_str(), "wb");

	int pid;
	unsigned long long kwd;
	set<int> neighborI;
	vector<edgeSegment> region; 
	map<edgeSegment, vector<int>, Compare> neighbor;
	map<edgeSegment, vector<float>, Compare> borderTpoiborder;

	for (int i = NodeNum; i < poiNodeNum; i++) {
		vcell vc = nvd[i];
		// 保存pid
		pid = vc.pid;
		fwrite(&pid, sizeof(int), 1, fout);
		// 保存kwd;
		kwd = vc.kwd;
		fwrite(&kwd, sizeof(unsigned long long), 1, fout);
		// 保存neighborI
		neighborI = vc.neighborI;
		int size = neighborI.size();
		fwrite(&size, sizeof(int), 1, fout);
		set<int> ::iterator its = neighborI.begin();
		for (; its != neighborI.end(); its++) {
			int nb = *its;
			fwrite(&nb, sizeof(int), 1, fout);
		}
		// 保存region
		region = vc.region;
		size = region.size();
		fwrite(&size, sizeof(int), 1, fout);
		for (int j = 0; j < size; j++) {			
			int ni = region[j].ni;
			int nj = region[j].nj;
			float start = region[j].start;
			float end = region[j].end;
			float border = region[j].border;
			fwrite(&ni, sizeof(int), 1, fout);
			fwrite(&nj, sizeof(int), 1, fout);
			fwrite(&start, sizeof(float), 1, fout);
			fwrite(&end, sizeof(float), 1, fout);
			fwrite(&border, sizeof(float), 1, fout);
		}

		// 保存neighbor
		neighbor = vc.neighbor;
		size = neighbor.size();
		fwrite(&size, sizeof(int), 1, fout);
		map<edgeSegment, vector<int>, Compare>::iterator itn = neighbor.begin();
		for (; itn != neighbor.end(); itn++) {
			edgeSegment es = itn->first;
			int ni = es.ni;
			int nj = es.nj;
			float start = es.start;
			float end = es.end;
			float border = es.border;
			fwrite(&ni, sizeof(int), 1, fout);
			fwrite(&nj, sizeof(int), 1, fout);
			fwrite(&start, sizeof(float), 1, fout);
			fwrite(&end, sizeof(float), 1, fout);
			fwrite(&border, sizeof(float), 1, fout);

			// 继续保存vector<int>
			vector<int> nbid = itn->second;
			int size2 = nbid.size();
			fwrite(&size2, sizeof(int), 1, fout);
			for (int j = 0; j < size2; j++) {
				int nid = nbid[j];
				fwrite(&nid, sizeof(int), 1, fout);
			}
		}

		// 保存borderTpoiborder
		borderTpoiborder = vc.borderTpoiborder;
		size = borderTpoiborder.size();
		fwrite(&size, sizeof(int), 1, fout);
		map<edgeSegment, vector<float>, Compare>::iterator itnf = borderTpoiborder.begin();
		for (; itnf != borderTpoiborder.end(); itnf++) {
			edgeSegment es = itnf->first;
			int ni = es.ni;
			int nj = es.nj;
			float start = es.start;
			float end = es.end;
			float border = es.border;
			fwrite(&ni, sizeof(int), 1, fout);
			fwrite(&nj, sizeof(int), 1, fout);
			fwrite(&start, sizeof(float), 1, fout);
			fwrite(&end, sizeof(float), 1, fout);
			fwrite(&border, sizeof(float), 1, fout);

			// 继续保存vector<int>
			vector<float> nbidf = itnf->second;
			int size2 = nbidf.size();
			fwrite(&size2, sizeof(int), 1, fout);
			for (int j = 0; j < size2; j++) {
				float disf = nbidf[j];
				fwrite(&disf, sizeof(float), 1, fout);
			}
		}
	}
	fclose(fout);
	cout << "END saveNVD" << endl;
}

map<int, vcell> loadNVD(string filename) {
	//ofstream nvdOut(filename + "\\nvd");
	string pathnvd = filename + "\\nvd";
	FILE *fin = fopen(pathnvd.c_str(), "rb");

	map<int, vcell> nvdReturn;
	int pid;
	unsigned long long kwd;
	set<int> neighborI;
	vector<edgeSegment> region;
	map<edgeSegment, vector<int>, Compare> neighbor;
	map<edgeSegment, vector<float>, Compare> borderTpoiborder;

	//注意：这里的NodeNum和poiNodeNum可能都是未初始化的
	for (int i = NodeNum; i < poiNodeNum; i++) {
		vcell vc;
		// 读入pid
		fread(&pid, sizeof(int), 1, fin);
		// 读入kwd;
		fread(&kwd, sizeof(unsigned long long), 1, fin);
		// 读入neighborI
		neighborI.clear();
		int size;
		fread(&size, sizeof(int), 1, fin);		
		for (int j = 0; j < size; j++) {
			int nb;
			fread(&nb, sizeof(int), 1, fin);
			neighborI.insert(nb);
		}
		// 读入region
		region.clear();
		fread(&size, sizeof(int), 1, fin);
		for (int j = 0; j < size; j++) {
			int ni, nj;
			float start, end, border;
			fread(&ni, sizeof(int), 1, fin);
			fread(&nj, sizeof(int), 1, fin);
			fread(&start, sizeof(float), 1, fin);
			fread(&end, sizeof(float), 1, fin);
			fread(&border, sizeof(float), 1, fin);
			edgeSegment es;
			es.ni = ni;
			es.nj = nj;
			es.start = start;
			es.end = end;
			es.border = border;
			region.push_back(es);
		}

		// 读入neighbor
		neighbor.clear();
		fread(&size, sizeof(int), 1, fin);	
		for (int j = 0; j < size; j++) {
			int ni, nj;
			float start, end, border;
			fread(&ni, sizeof(int), 1, fin);
			fread(&nj, sizeof(int), 1, fin);
			fread(&start, sizeof(float), 1, fin);
			fread(&end, sizeof(float), 1, fin);
			fread(&border, sizeof(float), 1, fin);
			edgeSegment es;
			es.ni = ni;
			es.nj = nj;
			es.start = start;
			es.end = end;
			es.border = border;			

			// 继续读入vector<int>
			vector<int> nbid;
			nbid.clear();
			int size2;
			fread(&size2, sizeof(int), 1, fin);
			for (int k = 0; k < size2; k++) {
				int nid;
				fread(&nid, sizeof(int), 1, fin);
				nbid.push_back(nid);
			}
			neighbor[es] = nbid;
		}

		// 读入borderTpoiborder
		borderTpoiborder.clear();
		fread(&size, sizeof(int), 1, fin);
		
		for (int j = 0; j < size; j++) {
			int ni, nj;
			float start, end, border;
			fread(&ni, sizeof(int), 1, fin);
			fread(&nj, sizeof(int), 1, fin);
			fread(&start, sizeof(float), 1, fin);
			fread(&end, sizeof(float), 1, fin);
			fread(&border, sizeof(float), 1, fin);
			edgeSegment es;
			es.ni = ni;
			es.nj = nj;
			es.start = start;
			es.end = end;
			es.border = border;			

			// 继续读入vector<int>
			vector<float> nbidf;
			nbidf.clear();
			int size2;
			fread(&size2, sizeof(int), 1, fin);
			for (int k = 0; k < size2; k++) {
				float disf;
				fread(&disf, sizeof(float), 1, fin);
				nbidf.push_back(disf);
			}
			borderTpoiborder[es] = nbidf;
		}

		vc.pid = pid;
		vc.kwd = kwd;
		vc.neighborI = neighborI;
		vc.region = region;
		vc.neighbor = neighbor;
		vc.borderTpoiborder = borderTpoiborder;
		nvdReturn[i] = vc;
	}
	fclose(fin);
	return nvdReturn;
}

// 将reAdjlist保存在硬盘上方便访问
void saveAdjList(string filename) {
	cout << "start saveAdjList" << endl;
	int curtaddress = 0;
	ofstream assOut(filename + "\\reAddress");
	string pathadj = filename + "\\reAdjlist";
	FILE *fout = fopen(pathadj.c_str(), "wb");
	
	for (int i = 0; i < poiNodeNum; i++) {
		address[i] = curtaddress;
		map<int, float> nb = reAdjList[i];
		int size = nb.size();
		fwrite(&size, sizeof(int), 1, fout);
		map<int, float> ::iterator itnb = nb.begin();
		for (; itnb != nb.end(); itnb++) {
			int nid = itnb->first;
			float dist = itnb->second;
			fwrite(&nid, sizeof(int), 1, fout);
			fwrite(&dist, sizeof(float), 1, fout);
		}
		curtaddress = curtaddress + sizeof(int) * (size + 1) + sizeof(float) * size;
		assOut << i << " " << address[i] << endl;
	}
	fclose(fout);
	assOut.close();
	cout << "end saveAdjList" << endl;
}

map<int,int> loadAddress(string filename) {
	map<int, int> addrs;
	ifstream iFile(filename + "\\reAddress");
	string line;
	while (!iFile.eof()) {
		getline(iFile, line);
		if (line == "") continue;
		int id, addr; 
		istringstream iss(line);
		// --M-- read the unrelevant coordinates 
		iss >> id >> addr;
		addrs[id] = addr;
	}
	return addrs;
}

void saveReEdgeMap(string filename) {	
	cout << "start saveReEdgeMap" << endl;
	int size, pid;
	float dist;
	unsigned long long key;
	ofstream oFile(filename + "\\reEdgeMap");
	map<unsigned long long, vector<edgePoi>>::iterator it = reEdgeMap.begin();
	for (; it != reEdgeMap.end(); it++) {
		key = it->first;
		vector<edgePoi> temp = it->second;
		size = temp.size();
		oFile << key << " " << size;
		
		for (int i=0;  i<size; i++) {
			pid = temp[i].pid;
			dist = temp[i].dist;
			oFile << " " << pid << " " << dist;
		}
		oFile << endl;
	}
	oFile.close();
	cout << "end saveReEdgeMap" << endl;
}
        
map<unsigned long long, vector<edgePoi>> loadReEdgeMap(string filename) {
	unsigned long long key;
	int size, pid;
	float dist;
	map<unsigned long long, vector<edgePoi>> reEdgeMap;
	
	ifstream iFile(filename + "\\reEdgeMap");
	string line;
	while (!iFile.eof())
	{
		unsigned long long key;
		int size;
		getline(iFile, line);
		if (line == "") continue;
		istringstream iss(line);
		iss >> key >> size;
		vector<edgePoi> temp;
		for (int i = 0; i < size; i++) {			
			iss >> pid >> dist;
			edgePoi ep;
			ep.pid = pid;
			ep.dist = dist;
			temp.push_back(ep);
		}
		reEdgeMap[key] = temp;
	}
	return reEdgeMap;
}

void release() {
	// 释放Address
	map<int, int>().swap(address);
	address.clear();
	// 释放reAdjList
	map<int, map<int, float>> ::iterator itr = reAdjList.begin();
	for (; itr != reAdjList.end(); itr++) {
		map<int, float>().swap(itr->second);
		itr->second.clear();
	}
	map<int, map<int, float>>().swap(reAdjList);
	reAdjList.clear();
	// 释放reEdgeMap
	map<unsigned long long, vector<edgePoi>>::iterator ite = reEdgeMap.begin();
	for (; ite != reEdgeMap.end(); ite++) {
		vector<edgePoi>().swap(ite->second);
		ite->second.clear();
	}
	map<unsigned long long, vector<edgePoi>>().swap(reEdgeMap);
	reEdgeMap.clear();

	// 释放nvd
	map<int, vcell>::iterator itn = nvd.begin();
	for (; itn != nvd.end(); itn++) {
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
	map<int, vcell>().swap(nvd);
	nvd.clear();
}

void saveVANN(string filename) {
	saveNVD(filename);
	saveAdjList(filename);
	saveReEdgeMap(filename);
	release();
}