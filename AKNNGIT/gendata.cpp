#include "gendata.h"
#include "utility.h"
#include "netshare.h"
#include "egtree.h"
#include "netVornonoi.h"
#include "KeywordsGenerator.h"
#include <sstream>
//#pragma comment(lib,"ws2_32.lib")

#define MAX_KEYWORDSN 64
#define MAXLEVEL 10
#define MAXKWD 64
#define WEIGHT_FACTOR 1

// to be initialized
char **cur_block;
int *cur_block_offset, *cur_node_maxkey, *cur_node_entries;
char *block;
int  root_block_id, num_written_blocks, top_level;
extern int BlkLen;
extern int i_capacity;

int PtMaxKey = 0;
bool PtMaxUsing = false;	// for solving the bug that was to find
float FACTOR;
bool IS_NODE_SIZE_GIVEN = false;

int num_D;
int num_K;


float STEP_SIZE;
float MAX_SEG_DIST;
float AVG_DEG;
extern vector <TreeNode> EGTree;
extern int poiNodeNum;
//extern map<int, unsigned long long> iTedge; 
//extern map<unsigned long long, int> edgenum;

struct PartAddr {
	int part;
	int addr;
};
map<int, PartAddr> partID;

BTree* initialize(char *treename)
{
	BTree *bt;

	cur_block = new char*[MAXLEVEL]; //ptr to current node at each level
	cur_block_offset = new int[MAXLEVEL];
	cur_node_maxkey = new int[MAXLEVEL];
	cur_node_entries = new int[MAXLEVEL];
	top_level = 0;

	for (int i = 0; i<MAXLEVEL; i++) cur_block[i] = NULL;
	block = new char[BlkLen];

	// number of cached file entries: 128
	bt = new BTree(treename, BlkLen, 128);
	i_capacity = (BlkLen - sizeof(char) - sizeof(int)) / (sizeof(int) + sizeof(int));
	printf("i_capacity=%d\n", i_capacity);
	root_block_id = bt->root_ptr->block;
	num_written_blocks = 0;
	return  bt;
}

void addentry(BTree *bt, int *top_level, int capacity, int level, int key, int *block_id, int RawAddr)
{
	if (cur_block[level] == NULL)   //new node to be created
	{
		if ((*top_level) < level) //new root
			*top_level = level;
		cur_block[level] = new char[BlkLen];

		char l = (char)level;
		memcpy(cur_block[level], &l, sizeof(char));

		cur_block_offset[level] = sizeof(char) + sizeof(int);
		cur_node_entries[level] = 0;
	}
	cur_node_maxkey[level] = key;
	if ((level == 1) && PtMaxUsing) cur_node_maxkey[level] = PtMaxKey>key ? PtMaxKey : key;//Modified by Qin Xu

																						   //copy key as new current entry and also the pointer to lower node
	memcpy(cur_block[level] + cur_block_offset[level], &key, sizeof(int));
	cur_block_offset[level] += sizeof(int);

	//********* (Xblock_id for raw sequential page !)
	int Xblock_id = (level == 1) ? (RawAddr) : (*block_id);
	memcpy(cur_block[level] + cur_block_offset[level], &Xblock_id, sizeof(int));

	cur_block_offset[level] += sizeof(int);
	cur_node_entries[level]++;

	if (cur_node_entries[level] == capacity)   //node is full
	{
		//copy capacity information
		memcpy(cur_block[level] + sizeof(char), &capacity, sizeof(int));
		//add maxkey of this node to upper level node
		bt->file->append_block(cur_block[level]);
		(*block_id)++;
		bt->num_of_inodes++;
		addentry(bt, top_level, capacity, level + 1,
			cur_node_maxkey[level], block_id, 0);
		delete[] cur_block[level];
		cur_block[level] = NULL;
	}
}

void finalize(BTree* bt)
{
	//flush non-empty blocks
	for (int level = 1; level <= top_level; level++)
	{
		if (cur_block[level] != NULL)
		{
			//copy capacity information
			memcpy(cur_block[level] + sizeof(char), &cur_node_entries[level], sizeof(int));
			//add mbr of this node to upper level node
			if (level == top_level)
			{
				//root
				bt->file->write_block(cur_block[level], root_block_id);
				bt->num_of_inodes++;
				bt->root_ptr = NULL;
				bt->load_root();
				//printf("root written, id=%d\n", root_block_id);
			}
			else
			{
				bt->file->append_block(cur_block[level]);
				num_written_blocks++;
				bt->num_of_inodes++;
				addentry(bt, &top_level, i_capacity, level + 1,
					cur_node_maxkey[level], &num_written_blocks, 0);
			}
			delete[] cur_block[level];
			cur_block[level] = NULL;
		}
	}
	delete[] block;
}
//Add by Qin Xu for sort InerNode purpose
struct ComparInerNode
{
	bool operator () (const InerNode& left, const InerNode& right) const
	{
		return left.dis > right.dis;
	}
};
// for the TDKD2005 paper algorightms TA and CE
// Pt FlatFile Field:
//		Header:	Ni(int), Nj(int), dist(float), size(int)
//		Entry:	vP(float)

bool cmpInternode (const InerNode& left, const InerNode& right) 
{
	return left.dis < right.dis;
}

void makePtFiles(FILE *ptFile, char* treefile) {
	PtMaxUsing = true;
	BTree* bt = initialize(treefile);
	printf("making PtFiles\n");

	int RawAddr = 0, key = 0, size;	// changed
	int nodesize = 0;
	int numedge = 0;
	EdgeMapType::iterator iter = EdgeMap.begin();
	while (iter != EdgeMap.end()) {
		edge* e = iter->second;
		numedge++;
		if (e->pts.size()>0) {	// do not index empty groups
			nodesize += e->pts.size();
			//在其他地方已经sort过了
			// sort(e->pts.begin(), e->pts.end(), cmpInternode);
			//sort(EGTree[treeNodeID].leafnodes.begin(), EGTree[treeNodeID].leafnodes.end(), less<int>());
			RawAddr = ftell(ptFile);	// set addr to correct amt.
			size = e->pts.size();
			fwrite(&(e->Ni), 1, sizeof(int), ptFile);
			fwrite(&(e->Nj), 1, sizeof(int), ptFile);
			fwrite(&(e->dist), 1, sizeof(float), ptFile);

			fwrite(&(size), 1, sizeof(int), ptFile);
			fwrite(&(e->pts[0]), e->pts.size(), sizeof(InerNode), ptFile); //???????????是不是要修改
			e->FirstRow = key;
			PtMaxKey = key + e->pts.size() - 1;	// useful for our special ordering !									//printf("(key,value)=(%d,%d)\n",key,RawAddr);

			addentry(bt, &top_level, i_capacity, 1, key, &num_written_blocks, RawAddr);
			key += sizeof(int) * 3 + sizeof(float);
			key += size * sizeof(InerNode); //Modified by Qin Xu
		}
		else
			e->FirstRow = -1;		// also later used by AdjFile
		iter++;
	}
	printf("Build-pt The number of edge is:%d\n", numedge);
	printf("Build-pt The number of pt is:%d\n", nodesize);
	finalize(bt);
	bt->UserField = num_D;
	delete bt;
	PtMaxUsing = false;
}

//int PTGRP_HEADSIZE = 3 * sizeof(int) + sizeof(float);
//int PTGRP_ITEMSIZE = sizeof(float);
int HEADSIZE = sizeof(int);
int ITEMSIZE = 2 * sizeof(int) + sizeof(float) + sizeof(unsigned long long);

void makeAdjListFiles(FILE *alFile) {
	printf("making alFiles, dependency on makePtFiles\n");

	int key = 0, size, PtSize;
	fwrite(&NodeNum, 1, sizeof(int), alFile);

	// slotted header info.
	int addr = sizeof(int) + sizeof(int)*NodeNum;
	for (int Ni = 0; Ni<NodeNum; Ni++) {
		fwrite(&addr, 1, sizeof(int), alFile);
		addr += HEADSIZE + AdjList[Ni].size()*ITEMSIZE;
	}

	float distsum = 0;
	for (int Ni = 0; Ni<NodeNum; Ni++) {
		// write Ni's crd, added at 28/1/2004
		//fwrite(&(xcrd[Ni]), 1, sizeof(float), alFile);
		//fwrite(&(ycrd[Ni]), 1, sizeof(float), alFile);

		size = AdjList[Ni].size();
		fwrite(&(size), 1, sizeof(int), alFile);
		unsigned long long nie = Ni;
		for (int k = 0; k<AdjList[Ni].size(); k++) {
			int Nk = AdjList[Ni][k];	// Nk can be smaller or greater than Ni !!!

			unsigned long long nke = Nk;
			unsigned long long key = getKey(nie, nke);
			edge* e = EdgeMap[key];
			PtSize = e->pts.size();

			fwrite(&Nk, 1, sizeof(int), alFile);
			fwrite(&(e->dist), 1, sizeof(float), alFile);
			fwrite(&(e->sumkwds), 1, sizeof(unsigned long long), alFile);
			fwrite(&(e->FirstRow), 1, sizeof(int), alFile); // use FirstRow for other purpose ... 
			//printf("(Ni,Nj,dataAddr)=(%d,%d,%d)\n",Ni,Nk,e->FirstRow);
			distsum += e->dist;
		}
		key = Ni;
	}
	distsum = distsum / 2;
	printf("total edge dist: %f\n", distsum);
}

void BuildBinaryStorage(string fileprefix) {
	BlkLen = getBlockLength();
	char tmpFileName[255];

	FILE *ptFile, *edgeFile;
	string name;
	name = fileprefix + "\\pfile_tkde";
	remove(name.c_str()); // remove existing file
	ptFile = fopen(name.c_str(), "wb+");
	name.clear();
	name = fileprefix + "\\pbtree_tkde";
	//sprintf(tmpFileName,"%s\\pbtree",fileprefix);
	//remove(tmpFileName); // remove existing file
	remove(name.c_str()); // remove existing file
	char* c;
	int len = name.length();
	c = new char[len + 1];
	strcpy(c, name.c_str());
	makePtFiles(ptFile, c);

	name.clear();
	name = fileprefix + "\\adjlist_tkde";

	remove(name.c_str()); // remove existing file
	edgeFile = fopen(name.c_str(), "wb+");
	makeAdjListFiles(edgeFile);

	// generate reserve the part and address information

	fclose(ptFile);
	fclose(edgeFile);
}

//------extend for egtree
void makeEPtFiles(FILE *ptFile, char* treefile) {
	// construct the extend point file
	set<unsigned long long> vEdgeKey;
	int sizep = sizeof(int) + sizeof(float) + sizeof(unsigned long long);
	PtMaxUsing=true;							 
	BTree* bt=initialize(treefile);
	printf("making EPtFiles\n");
	//------treeNode start from 0
	int treeNodeID = 0;
	int nodeID = 0;
	int RawAddr = 0, key = 0, size, PtSize;
	int numedge = 0;
	int nodesize = 0;
	for (; treeNodeID < EGTree.size(); treeNodeID++) {
		if (!EGTree[treeNodeID].isleaf) continue;
		// is leaf node ,sort it in ascend order
		sort(EGTree[treeNodeID].leafnodes.begin(), EGTree[treeNodeID].leafnodes.end(), less<int>());
		for (int i = 0; i<EGTree[treeNodeID].leafnodes.size(); i++) {
			nodeID = EGTree[treeNodeID].leafnodes[i];
			unsigned long long nid = nodeID;
			partID[nodeID].part = treeNodeID;
			// put the adjacent nodes of this node into adjList
			for (int j = 0; j<AdjList[nodeID].size(); j++) {
				int Nj = AdjList[nodeID][j];
				unsigned long long nje = Nj;
				// Nk can be smaller or greater than Ni !!!
				unsigned long long mapkey = getKey(nid, nje);
				if (vEdgeKey.find(mapkey) != vEdgeKey.end()) {// this edge has been visited
					continue;
				}
				vEdgeKey.insert(mapkey);
				numedge++;
				edge* e = EdgeMap[mapkey];			
				PtSize = e->pts.size();
				if (PtSize>0) {
					nodesize += PtSize;
					sort(e->pts.begin(), e->pts.end(), ComparInerNode());
					RawAddr = ftell(ptFile);	// set addr to correct amt.
					fwrite(&(e->Ni), 1, sizeof(int), ptFile);
					fwrite(&(e->Nj), 1, sizeof(int), ptFile);
					fwrite(&(e->dist), 1, sizeof(float), ptFile);
					fwrite(&(PtSize), 1, sizeof(int), ptFile);
					fwrite(&(e->pts[0]),e->pts.size(),sizeof(InerNode),ptFile); //???????????是不是要修改
					e->FirstRow = key;
					PtMaxKey = key + e->pts.size() - 1;	// useful for our special ordering !									//printf("(key,value)=(%d,%d)\n",key,RawAddr);
					
					addentry(bt, &top_level, i_capacity, 1, key, &num_written_blocks, RawAddr);
					key += sizeof(int) * 3 + sizeof(float);
					key += PtSize * sizeof(InerNode); //Modified by Qin Xu
				}
				else {
					e->FirstRow = -1; // also later used by AdjFile
				}

			}
		}
	}
	printf("Build-EHANCE-pt The number of edge is:%d\n", numedge);
	printf("Build-EHANCE-pt The number of pt is:%d\n", nodesize);
	finalize(bt);
	bt->UserField=num_D;
	delete bt;
	PtMaxUsing=false;
}

void makeEAdjListFiles(FILE *alFile) { // construct the extend adjacentList file

	printf("making EAdjListFiles\n");
	//------treeNode start from 0
	int treeNodeID = 0;
	int nodeID = 0;
	int size, addr = 0;
	float distsum = 0;
	fwrite(&NodeNum, 1, sizeof(int), alFile);

	// slotted header info.
	int addrss = sizeof(int);
	int adjFixsize = 2 * sizeof(int) + sizeof(float) + sizeof(unsigned long long);

	for (; treeNodeID < EGTree.size(); treeNodeID++) {
		if (!EGTree[treeNodeID].isleaf) continue;
		// is leaf node ,may be no use
		sort(EGTree[treeNodeID].leafnodes.begin(), EGTree[treeNodeID].leafnodes.end(), less<int>());
		for (int i = 0; i<EGTree[treeNodeID].leafnodes.size(); i++) {
			nodeID = EGTree[treeNodeID].leafnodes[i];
			unsigned long long nid = nodeID;
			partID[nodeID].addr = addrss;
			size = AdjList[nodeID].size();
			fwrite(&(size), 1, sizeof(int), alFile);
			addrss = addrss + sizeof(int);
			for (int k = 0; k<size; k++)
			{
				int Nk = AdjList[nodeID][k];	// Nk can be smaller or greater than Ni !!!
				unsigned long long Nke = Nk;
				unsigned long long keyv = getKey(nid, Nke);
				edge* e = EdgeMap[keyv];				

				fwrite(&Nk, 1, sizeof(int), alFile);
				fwrite(&(e->dist), 1, sizeof(float), alFile);
				fwrite(&(e->sumkwds), 1, sizeof(unsigned long long), alFile);
				// pointer information
				fwrite(&(e->FirstRow), 1, sizeof(int), alFile); // use FirstRow for other purpose ...
				
				distsum += e->dist;
			}
			addrss = addrss + adjFixsize * AdjList[nodeID].size();
		}
	}
	distsum = distsum / 2;
	printf("total edge dist: %f\n", distsum);
	//printf("total keywords num:%d\n",num_K);
}

void BuildEBinaryStorage(string fileprefix) { // construct the extend binary storage
	BlkLen = getBlockLength();
	char tmpFileName[255];

	FILE *ptFile, *edgeFile;
	string name;
	name = fileprefix + "\\pfile";
	remove(name.c_str()); // remove existing file
	ptFile = fopen(name.c_str(), "wb+");
	name.clear();
	name = fileprefix + "\\pbtree";
	//sprintf(tmpFileName,"%s\\pbtree",fileprefix);
	//remove(tmpFileName); // remove existing file
	remove(name.c_str()); // remove existing file
	char* c;
	int len = name.length();
	c = new char[len + 1];
	strcpy(c, name.c_str());
	makeEPtFiles(ptFile, c);

	name.clear();
	name = fileprefix + "\\adjlist";

	remove(name.c_str()); // remove existing file
	edgeFile = fopen(name.c_str(), "wb+");
	makeEAdjListFiles(edgeFile);

	// generate reserve the part and address information
	partAddrSave(fileprefix);

	fclose(ptFile);
	fclose(edgeFile);
}


void partAddrSave(string fileprefix) {

	printf("making partAddrFile\n");
	//FILE *paFile;
	char tmpFileName[255];
	string name;
	name = fileprefix + "\\partAddr";
	//sprintf(tmpFileName, "%s\\partAddr", fileprefix);
	remove(name.c_str()); // remove existing file
	ofstream paFile(name.c_str());
	//ofstream owFile(objwetFile.c_str());
	//fwrite(&NodeNum, 1, sizeof(int), paFile);
	map<int, PartAddr>::iterator my_Itr;
	int num = partID.size();
	int i = 0;
	for (my_Itr = partID.begin(); my_Itr != partID.end(); ++my_Itr) {
		int first, pt, addr;
		first = my_Itr->first;
		pt = my_Itr->second.part;
		addr = my_Itr->second.addr;

		paFile << first << " " << pt << " " << addr << endl;

		//fwrite(&first, sizeof(int), 1, paFile);
		//fwrite(&pt, sizeof(int), 1, paFile);
		//fwrite(&addr, sizeof(int), 1, paFile);
		printf("i:%d, nodeid:%d, part:%d, addr:%d\n", i, my_Itr->first, my_Itr->second.part, my_Itr->second.addr);
		i++;
	}
	//fclose(paFile);
	paFile.close();
}

FastArray<float> xcrd, ycrd;

// future work: normalization of edge weight, reassign edge weight, divide into bands ...
// how about scanning whole file and putting edges with both nodeIDs in range ...
void ReadRealNetwork(std::string prefix_name, int _NodeNum)
{
	int eid, Ni, Nj;
	//int eid;
	float dist, x, y;
	//unsigned int Ni, Nj;
	string roadf;
	roadf = prefix_name + "\\edge";
	string outFile = prefix_name + "\\candquery";
	ofstream oFile(outFile.c_str());
	FILE* roadp = fopen(roadf.c_str(), "r");
	CheckFile(roadp, roadf.c_str());

	NodeNum = 0; // getKey depends on NodeNum so we have to init. it first
				 // vertex num start from 0
	while (!feof(roadp)) {
		fscanf(roadp, "%d %d %d %f\n", &eid, &Ni, &Nj, &dist);
		NodeNum = std::max(std::max(Ni, Nj), NodeNum);
	}
	NodeNum++;
	printf("%d nodes read, ", NodeNum);
	PrintElapsed();
	set<int> edgeid;
	fseek(roadp, 0, SEEK_SET);
	AdjList = new FastArray<int>[NodeNum];
	EdgeNum = 0;
	EdgeMap.clear();
	int loop = 0;
	vector<unsigned long long> vist;
	while (!feof(roadp))
	{
		fscanf(roadp, "%d %d %d %f\n", &eid, &Ni, &Nj, &dist);
		if (Ni < NodeNum && Nj < NodeNum)  	// ignore edges outside the range
		{
			//printf( "%d %d %d %f\n", id, Ni, Nj, dist);
			unsigned long long  a = Ni;
			unsigned long long  b = Nj;
			unsigned long long key = getKey(a, b);
			
			if (find(vist.begin(), vist.end(), key) != vist.end()) {
				continue;
			}
			vist.push_back(key);
			edge* e = new edge;
			//e->dist = dist;
			int distint;
			distint = (int)(dist * WEIGHT_FACTOR);
			e->dist = distint;
			e->Ni = Ni<Nj ? Ni : Nj;
			e->Nj = Ni<Nj ? Nj : Ni;	// enforce the constriant Ni<Nj
			AdjList[Ni].push_back(Nj);
			AdjList[Nj].push_back(Ni);

			//if(EdgeMap[key]->FirstRow)
			int vists = vist.size();
			//printf(" %d\n", vists);
			EdgeMap[key] = e;	// should be ok
			EdgeNum++;

			int randI = rand();
			if ((randI % 100) < 10) {
				oFile << key << " " << Ni << " " << Nj << " " << distint <<endl;
			}
		}
	}

	fclose(roadp);
	oFile.close();
}

void genPairByAd(int& Ni, int& Nj, int  avgPoints)
{
	int Ri, Rj;
	bool useNormalGenerator = true;	// use a ... generator
	int thre = avgPoints * 2;
	//srand((unsigned)time(NULL));
	if (useNormalGenerator)
	{
		do
		{
			//int num1 = rand();
			//int num2 = rand();
			Ri = rand() % NodeNum;
		} while (AdjList[Ri].size() == 0);
		//int n1 = rand();
		//int n2 = rand();
		int randn = rand() % AdjList[Ri].size();
		Rj = AdjList[Ri][randn];
		
	}
	Ni = Ri<Rj ? Ri : Rj;
	Nj = Ri<Rj ? Rj : Ri;
}

void printBinary(unsigned long long n)
{
	for (int i = MAX_KEYWORDS - 1; i >= 0; i--)
		cout << ((n >> i) & 1);
	cout<<endl;
}

//void GenOutliers(int EdgeNum, int avgPoints, int avgKeywords)
//{
//	int NumPoint = EdgeNum*avgPoints;
//	std::vector<unsigned long long> keys = KeywordsGenerator::Instance().getKeywords(NumPoint, avgKeywords);
//	int Ni, Nj;
//	num_K = 0;
//	num_D = NumPoint;
//	//srand((unsigned)time(NULL));
//	for (int z = 0; z<NumPoint; z++)
//	{
//		//printf("Point is %d\n", z);
//		genPairByAd(Ni, Nj, avgPoints);
//
//		unsigned long long vni, vnj, key;
//		vni = Ni;
//		vnj = Nj;
//		key = getKey(vni, vnj);
//		
//		//int loopid = rand() % EdgeMap.size();
//		//int loopid = time(NULL) % EdgeMap.size();
//		//key = iTedge[loopid];
//		//if(edgenum)
//		// used to balance the points on the edge
//		/*if (edgenum.find(key) != edgenum.end()) {
//			if (edgenum[key] > 2 * avgPoints) {
//				z--;
//				continue;
//			}
//			edgenum[key] ++;
//		}
//		else {
//			edgenum[key] = 1;
//		}*/
//		edge* e = EdgeMap[key];
//		// 确保POI不落在vertex上
//		int randT = 0;
//		while (randT == 0 || randT == RAND_MAX) {
//			randT = rand();
//		}
//		float vP = (randT*e->dist)/RAND_MAX;
//		num_K += std::bitset<64>(keys[z]).count();
//		unsigned long long tmpvct = keys[z];
//		InerNode tempNode;
//		tempNode.pid = z;
//		tempNode.dis = vP;
//		tempNode.vct = tmpvct;
//		//e->pts.push_back(tempNode);
//		// -add sumkwds-
//		if (e->pts.size() > 0) {
//			e->sumkwds = e->sumkwds | tmpvct;
//		}
//		else {
//			e->sumkwds = tmpvct;
//		}		
//		e->pts.push_back(tempNode);
//#ifdef _TEST
//		cout << "(" << Ni << "," << Nj << ")" << " ";
//		cout << bitset<64>(tmpvct).to_string() << endl;
//#endif
//
//	}
//
//	// spread outliers based on distance
//	// work for connected graph, may not work for disconnected graphs
//	// organize dist based on length and then ...
//	int looppt = 0;
//	EdgeMapType::iterator it = EdgeMap.begin();
//	for (; it != EdgeMap.end(); it++) {
//		edge* e = it->second;
//		if (e->pts.size() < 1) looppt++;
//		//printf("pt num is %d\n", e->pts.size());
//	}
//	printf("pt num is %d\n", looppt);
//	printf("edge size is %d\n", EdgeMap.size());
//}

// 生成POI点并将POI点对应的顶点的信息保存起来POI，便于后面插入删除操作处理
void GenOutliers(int EdgeNum, int avgPoints, int avgKeywords, string fileprefix)
{
	// 将POI信息保存在文件中
	printf("making poiFile\n");
	//FILE *paFile;
	char tmpFileName[255];
	string name;
	name = fileprefix + "\\poiFile";
	//sprintf(tmpFileName, "%s\\partAddr", fileprefix);
	remove(name.c_str()); // remove existing file
	ofstream poiFile(name.c_str());


	int NumPoint = EdgeNum*avgPoints;
	std::vector<unsigned long long> keys(NumPoint, 0);
	//keys = KeywordsGenerator::Instance().getKeywords(NumPoint, avgKeywords, keys);
	KeywordsGenerator::Instance().getKeywords(NumPoint, avgKeywords, keys);
	//int Ni, Nj;
	int keysize = keys.size();
	printf("size is %d\n", keysize);
	num_K = 0;
	num_D = 0;
	//srand((unsigned)time(NULL));
	EdgeMapType::iterator it = EdgeMap.begin();
	int nOfp = 0;
	for (; it != EdgeMap.end(); it++) {
		edge* e = it->second;
		int npt = KeywordsGenerator::Instance().getNumOfPoints(avgPoints);
		num_D += npt;
		int right = (int)(e->dist*0.98);
		int vi, vj;
		unsigned long long key = it->first;
		breakKey(key,vi,vj);
		set<int> exitDist;
		for (int l = 0; l < npt; l++) {
			int dst;
			//isContinue = true;
			while (true) {
				dst = (int)((rand()*right) / RAND_MAX);
				//int right = (int)(e->dist - 2);
				if (dst>0 && e->dist) {
					if(exitDist.find(dst) == exitDist.end()) break;
				}
			}
			
			int id = nOfp % NumPoint;
			num_K += std::bitset<64>(keys[id]).count();
			
			unsigned long long tmpvct = keys[id];
			InerNode tempNode;
			tempNode.pid = nOfp;
			tempNode.dis = dst;
			tempNode.vct = tmpvct;
			exitDist.insert(dst);
			// 输出POI信息
			poiFile << nOfp << " " << vi << " " << vj << endl;

			if (e->pts.size() > 0) {
				e->sumkwds = e->sumkwds | tmpvct;
			}
			else {
				e->sumkwds = tmpvct;
			}
			e->pts.push_back(tempNode);
			nOfp++;
		}		
		// 修改在这里，主要是在这里进行了排序，主要是为了后面VANN进行访问预处理
		sort(e->pts.begin(), e->pts.end(), cmpInternode);
	}
	poiFile.close();
	poiNodeNum = NodeNum + nOfp;
	printf("edge size is %d\n", EdgeMap.size());
}

void ConnectedGraphCheck()
{
	BitStore isVisited;
	isVisited.assign(NodeNum, false);

	StepQueue sQ;
	StepEvent stepX;
	stepX.node = 0;
	sQ.push(stepX);

	int cnt = 0;
	while (!sQ.empty())  	// beware of infty loops
	{
		StepEvent event = sQ.top();
		sQ.pop();
		if (isVisited[event.node]) continue;
		isVisited[event.node] = true;
		cnt++;
		int Ni = event.node;
		for (int k = 0; k<AdjList[Ni].size(); k++)
		{
			int Nk = AdjList[Ni][k];	// Nk can be smaller or greater than Ni !!!
			if (!isVisited[Nk])
			{
				StepEvent newevent = event;
				newevent.node = Nk;
				sQ.push(newevent);
			}
		}
	}

	if (cnt == NodeNum)
		cout << "Road Network is Connected." << endl;
	else
		cout << "Road Network is not Connected." << endl;
}

void getOutliersFromFile(char* prefix_name)
{
	int Ni, Nj;
	int NumOutliers = 0;
	char tmpf[255];
	sprintf(tmpf, "%smap.txt", prefix_name);
	float dist;
	int num;
	unsigned long long keyword;
	float tmpdist;

	FILE* calf = fopen(tmpf, "r");
	CheckFile(calf, tmpf);

	while (!feof(calf))
	{
		fscanf(calf, "%d %d %f %d\n", &Ni, &Nj, &dist, &num);
		for (int i = 0; i<num; ++i)
		{
			fscanf(calf, "%llu %f", &keyword, &tmpdist);
			edge* e = EdgeMap[getKey(Ni, Nj)];
			InerNode tmpNode;
			tmpNode.dis = tmpdist;
			tmpNode.vct = keyword>1 ? keyword : 1;//keywords must less than MAX and more than zero
			e->pts.push_back(tmpNode);
			NumOutliers++;
		}
	}
	num_D = NumOutliers;

	//cout << "Total Num of Outliers Read From File:" << cnt << endl;
	// spread outliers based on distance
	// work for connected graph, may not work for disconnected graphs
	// organize dist based on length and then ...
}

//从POI文件中读取信息并输出到operation文件
void generateOperation(string fileprefix, int num) {// ratio 指定需要访问总数的多少
	// 将POI信息从文件中读取出来
	printf("generate operations!\n");
	//FILE *paFile;
	char tmpFileName[255];
	string namePoi,nameOperation;
	namePoi = fileprefix + "\\poiFile";
	nameOperation = fileprefix + "\\operationFile";
	//sprintf(tmpFileName, "%s\\partAddr", fileprefix);
	remove(nameOperation.c_str()); // remove existing file
	ifstream iFile(namePoi.c_str());
	ofstream oFile(nameOperation.c_str());

	vector<poiPair> poiVector;
	poiVector.clear();

	string line;
	while (!iFile.eof())
	{
		getline(iFile, line);
		if (line == "") continue;
		int pid, vi, vj;
		istringstream iss(line);
		// --M-- read the unrelevant coordinates 
		iss >> pid >> vi >> vj;
		poiPair pp;
		pp.pid = pid;
		pp.vi = vi;
		pp.vj = vj;
		poiVector.push_back(pp);
	}
	iFile.close();
	int nOfPoi = poiVector.size();
	int nOfTotalOperation = num;
	int nOfDelete, nOfInsert;

	// 输出总的操作次数
	//oFile << nOfTotalOperation << endl;
	vector<int> intset;
	intset.clear();
	for (int i = 0; i < 10000; i++) {
		int randd = rand() % 131313;
		intset.push_back(randd);
	}
	// 生成5组测试数据，每组总数为nOfTotalOperation
	for (int l = 0; l < 1; l++) {
		float dRatio = 0.5;
		nOfDelete = nOfTotalOperation * dRatio;
		nOfInsert = nOfTotalOperation - nOfDelete;
		srand((unsigned)time(NULL));
		std::vector<unsigned long long> keys(nOfInsert, 0);
		//keys = KeywordsGenerator::Instance().getKeywords(NumPoint, avgKeywords, keys);
		KeywordsGenerator::Instance().getKeywords(nOfInsert, 6, keys);
		int nOfI = nOfInsert;
		int dPercent = dRatio * 100;
		int insertID = nOfPoi;
		set<int> deleteSet;
		set<int> insertSet;
		deleteSet.clear();
		insertSet.clear();
		int lnum = 0;
		while (nOfDelete || nOfInsert) {
			//srand((unsigned)time(NULL));
			// 如果两个操作都没完成，那么随机生成一个
			cout << "The loop num is :" << lnum << endl;
			if (nOfDelete && nOfInsert) {
				int percent = rand() % 100;
				if (percent <= dPercent) {// 生成删除
					//int deleteID;
					while (true) {
						int randnum = rand() % 10000;
						randnum = intset[randnum];
						int deleteID = (rand()*randnum) % nOfPoi;
						//deleteID++;
						cout << deleteID << endl;
						if (deleteSet.find(deleteID) == deleteSet.end()) {
							deleteSet.insert(deleteID);
							if (poiVector.size() <= deleteID) {
								cout << "GenerateOperation error" << endl;
								return;
							}
							oFile << 0 << " " << poiVector[deleteID].pid << " " << poiVector[deleteID].vi << " " << poiVector[deleteID].vj << endl;						
							break;
						}
					}
					nOfDelete--;
				}
				else { // 生成插入									
					while (true) {
						int randnum = rand() % 10000;
						randnum = intset[randnum];
						int pid = (rand()*randnum) % nOfPoi;
						cout << pid << endl;
						if (insertSet.find(pid) == insertSet.end()) {
							insertSet.insert(pid);
							if (poiVector.size() <= pid) {
								cout << "GenerateOperation error" << endl;
								return;
							}
							float dist = (rand() % 1000) * dRatio;
							int num = rand()%nOfI;
							unsigned long long word = keys[num];
							oFile << 1 << " " << insertID << " " << poiVector[pid].vi << " " << poiVector[pid].vj << " " << dist << " " << word << endl;
							insertID++;
							break;
						}
					}
					nOfInsert--;
				}
			}
			else if (nOfDelete) {// 生成删除操作
				while (true) {
					int randnum = rand() % 10000;
					randnum = intset[randnum];
					int deleteID = (rand()*randnum) % nOfPoi;
					cout << deleteID << endl;
					if (deleteSet.find(deleteID) == deleteSet.end()) {
						deleteSet.insert(deleteID);
						if (poiVector.size() <= deleteID) {
							cout << "GenerateOperation error" << endl;
							return;
						}
						oFile << 0 << " " << poiVector[deleteID].pid << " " << poiVector[deleteID].vi << " " << poiVector[deleteID].vj << endl;
						break;
					}
				}
				nOfDelete--;
			}
			else {// 生成插入操作
				while (true) {
					int randnum = rand() % 10000;
					randnum = intset[randnum];
					int pid = (rand()*randnum) % nOfPoi;
					cout << pid << endl;
					if (insertSet.find(pid) == insertSet.end()) {
						insertSet.insert(pid);
						if (poiVector.size() <= pid) {
							cout << "GenerateOperation error" << endl;
							return;
						}
						float dist = (rand() % 1000) * dRatio;
						int num = rand() % nOfI;
						unsigned long long word = keys[num];
						oFile << 1 << " " << insertID << " " << poiVector[pid].vi << " " << poiVector[pid].vj << " " << dist << " " << word << endl;
						insertID++;
						break;
					}
				}
				nOfInsert--;
			}
			lnum++;
		}
		oFile << endl << endl << endl << endl << endl;
		break;
	}
	oFile.close();
}

//int mainGenData(string prxfilename, roadParameter rp)
int mainGenData(string prxfilename)
{
	InitClock();	
	ReadRealNetwork(prxfilename, 0);
	
	ConnectedGraphCheck();
	GenOutliers(EdgeNum, 8, 6, prxfilename);
	printf("Avg keyword # per object:%f\n",float(num_K)/num_D);
	BuildBinaryStorage(prxfilename);

	//--------------------extend for VANN-------------------
	buildNVD(EdgeMap);
	saveVANN(prxfilename);
	//return 0;

	//--------------------extend for egtree-------------------
	mainEgtree(NodeNum, EdgeMap);
	BuildEBinaryStorage(prxfilename);
	egtree_save(prxfilename+"\\egtree");
	
	ofstream fout(prxfilename + "\\information");
	fout << NodeNum << " " <<poiNodeNum << endl;
	/*fout << "Number of Vertexes:" << NodeNum << endl;
	fout << "Number of Edges:" << EdgeNum << endl;
	fout << "Total Keyowords Number:" << num_K << endl;
	fout << "Total POIs Number:" << num_D << endl;
	fout << "Avg Keywords numbers per POI:" << float(num_K) / num_D << endl;*/
	fout.close();
	PrintElapsed();
	//*/
	return 0;
}

