#ifndef _GDATA_H_
#define _GDATA_H_

#include "btree.h"
#include "netshare.h"
#include <random>
#include<algorithm>
#include <bitset>
#include <vector>
#include<stdio.h>
using namespace std;
//------------
BTree* initialize(char *treename);
void addentry(BTree *bt, int *top_level, int capacity, int level, int key, int *block_id, int RawAddr);
void finalize(BTree* bt);
void makePtFiles(FILE *ptFile, char* treefile);
void makeAdjListFiles(FILE *alFile);
void BuildBinaryStorage(string fileprefix);
void makeEPtFiles(FILE *ptFile, char* treefile);
void makeEAdjListFiles(FILE *alFile);
void BuildEBinaryStorage(string fileprefix);
void partAddrSave(string fileprefix);
void ReadRealNetwork(string prefix_name, int _NodeNum);
void genPairByAd(int& Ni, int& Nj, int  avgPoints);
void printBinary(unsigned long long n);
void GenOutliers(int EdgeNum, int avgPoints, int avgKeywords, string fileprefix);
void ConnectedGraphCheck();
void getOutliersFromFile(char* prefix_name);
void generateOperation(string fileprefix, int num);
//int mainGenData(string prxfilename, roadParameter rp);
int mainGenData(string prxfilename);
#endif


