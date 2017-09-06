#pragma once
#include <vector>
#include <unordered_map>
#include "netshare.h"
using namespace std;
struct vertexAddr {
	int id;
	int address;
};

struct edgePoi {
	int pid;
	float dist;
};

struct edgeSegment {
	int ni;
	int nj;
	float start;
	float end;
	float border;
};

struct Compare
{
	int operator()(const edgeSegment& es1, const edgeSegment& es2) const {
		if (es1.ni >= es2.ni) {
			if (es1.ni > es2.ni) return false;
			else {
				if (es1.nj >= es2.nj) return false;
				else return true;
			}
		}
		else {
			return true;
		}
	}
};

struct label {
	float minDist;
	set<int> minSet;
};

struct vcell {
	int pid;
	unsigned long long kwd;
	vector<edgeSegment> region; // the borders of this node
	map<edgeSegment, vector<int>, Compare> neighbor; // 通过border来指向其他的相邻的VCell
	//vector<int> inerNodes;
	set<int> neighborI; // 记录neighbor的poi的id
	map<edgeSegment, vector<float>, Compare>borderTpoiborder; // 记录每个border到poi和其他border的距离
};




bool isEqual(edgeSegment es1, edgeSegment es2);
unordered_map<int, float> dijkstraBorder(int start, float disstart, int end, float disend, vector<int> cands);
void computeBorder();
void buildNVD(EdgeMapType EdgeMap);
void saveNVD(string filename);
map<int, vcell> loadNVD(string filename);
void saveAdjList(string filename);
map<int, int> loadAddress(string filename);
void saveReEdgeMap(string filename);
map<unsigned long long, vector<edgePoi>> loadReEdgeMap(string filename);
void saveVANN(string filename);