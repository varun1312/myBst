#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <stdint.h> 
#include <time.h>
#include <pthread.h>
#include <vector>
#include <thread>
#include <gsl/gsl_rng.h>
#include <gsl/gsl_randist.h>
#include <unistd.h>

const int LEFT = 0, RIGHT  = 1;
const int NORMAL = 0, MARKED = 1, PROMOTE = 2, REPLACE = 3;
const int DNORMAL = 0, DMARKED = 1;

const int NONNULL_NORMAL = 0, NONNULL_MARKED = 1, NONNULL_PROMOTE = 2, NULL_NORMAL = 4, NULL_MARKED = 5, NULL_PROMOTE = 6, NULL_REPLACE = 7;
volatile bool start = false, steadyState = false, stop = false;


#define ISNULL(node) (bool)((uintptr_t)node & 0x04)
#define GETADDR(node) ((Node *)((uintptr_t)node & ~0x07))
#define GETKEY(ptr) (*(int *)((uintptr_t)(ptr) & ~0x01))
#define STATUS(node) (int)((uintptr_t)node & 0x03) 
#define markNode(node, null, status) \
	(((uintptr_t)node & ~0x07) | (null << 2) | status) 

#define NODE_STATUS(node) ((uintptr_t)node & 0x07)
#define MARK_NODE(node, status) (Node *)(((uintptr_t)node & ~0x07) | status)
#define NODE_CAS(ptr, s, ss, t, ts) \
	__sync_bool_compare_and_swap(ptr, MARK_NODE(s, ss), MARK_NODE(t, ts))
#define DATA_ADDR(ptr) ((uintptr_t)ptr & ~0x01)
#define DATA_STAT(ptr) ((uintptr_t)ptr & 0x01)


#define CAS(ptr, s, sn, ss, t, tn, ts) \
	__sync_bool_compare_and_swap(ptr, markNode(s, sn, ss), markNode(t, tn, ts))
#define DCAS(ptr, s, ss, t, ts) \
	__sync_bool_compare_and_swap(ptr, (((uintptr_t)s & ~0x01) | ss), (((uintptr_t)t & ~0x01) | ts)) 



#define DEFAULT_DURATION 2
#define DEFAULT_DATA_SIZE 256
#define DEFAULT_THREADS 1
#define DEFAULT_RANGE 0x7FFFFFFF
#define DEFAULT_SEED 0
#define DEFAULT_INSERT 20
#define DEFAULT_REMOVE 10
#define DEFAULT_SEARCH 70

int duration = DEFAULT_DURATION;
int dataSize = DEFAULT_DATA_SIZE;
int numThreads = DEFAULT_THREADS;
int range = DEFAULT_RANGE;
unsigned int seed = DEFAULT_SEED;
int insertPer = DEFAULT_INSERT;
int removePer = DEFAULT_REMOVE;
int searchPer = DEFAULT_SEARCH;
int initialSize = ((dataSize)/2);

struct Node {
	Node *bl;
	int *keyPtr;
	Node *child[2];
};

Node *root = (Node *)malloc(sizeof(Node));

struct NodeLocation {
	Node *ancNode;
	Node *pred;
	Node *curr;
	int *ancKeyPtr;
	
	Node *newNode;
	bool isNewNodeAvailable;
	unsigned long insertCount;
	unsigned long deleteCount;
	unsigned long searchCount;
	int tid;
	unsigned long lseed;	

	Node *currTemp;
	Node *predTemp;
	NodeLocation(Node *ancNode, Node *pred, Node *curr, int *ancKeyPtr) {
		this->ancNode = ancNode;
		this->pred = pred;
		this->curr = curr;
		this->ancKeyPtr = ancKeyPtr;
	}
};


bool isPresentInTree(Node *node) {
	Node *par = node->bl;
	Node *rc = par->child[RIGHT];
	Node *lc = par->child[LEFT];
	bool rn = ISNULL(rc);
	bool ln = ISNULL(lc);
	if ((GETADDR(rc) == node && rn == false) || (GETADDR(lc) == node && ln == false))
		return true;
	return false;
}

bool isInvalidSearch(Node *node, int *keyPtr) {
	int *nodeKeyPtr = (int *)((uintptr_t)(GETADDR(node)->keyPtr) & ~0x01);
	if (nodeKeyPtr != ((int *)((uintptr_t)keyPtr & ~0x01)))
		return true;
	else if (node != root && isPresentInTree(node) == false)
		return true;
	return false;
}



bool removeTree(int, NodeLocation *);
bool markChildNodeAll(Node *, int , int , int );

void find(int key, NodeLocation *nodeLoc, Node *startNode, Node *_ancNode, int *_ancKeyPtr) {
	Node *curr = startNode;
	Node *pred = curr->bl;
	Node *ancNode = _ancNode;
	int *ancKeyPtr = ancKeyPtr, *currKeyPtr;
	bool n;	
	int currKey, lr, currStat;
	while(true) {
		currStat  = NODE_STATUS(curr);
		if (currStat == NULL_NORMAL || currStat == NULL_MARKED || currStat == NULL_PROMOTE || currStat == NULL_REPLACE) {
			if (isInvalidSearch(ancNode, ancKeyPtr)) {
				find(key, nodeLoc, root, root, root->keyPtr);
				return;
			}
			break;
		}
		currKeyPtr = (int *)((uintptr_t)(GETADDR(curr)->keyPtr) & ~0x01);
		currKey = GETKEY(currKeyPtr);	
		if (key == currKey)
			break;
		lr = key > currKey ? RIGHT : LEFT;
		if (lr == LEFT) {
			ancNode = GETADDR(curr);
			ancKeyPtr = currKeyPtr;
		}
		pred = GETADDR(curr);
		curr = GETADDR(curr)->child[lr];
	}
	nodeLoc->ancNode = ancNode;
	nodeLoc->ancKeyPtr = ancKeyPtr;
	nodeLoc->pred = pred;
	nodeLoc->curr = curr;	
}

bool removeNode(Node *, Node *, int, NodeLocation *);

bool markNullChildOnly(Node *node, int lr, int status, int *keyPtr) {
	Node *child;
	int childStat;
	while(true) {
		child = node->child[lr];
		childStat = NODE_STATUS(child);
		if (childStat == NONNULL_NORMAL)
			return false;
		else if (childStat == NONNULL_MARKED || childStat == NULL_MARKED || childStat == NULL_PROMOTE || childStat == NONNULL_PROMOTE)
			return true;
		else if (childStat == NULL_NORMAL) {
			if (NODE_CAS(&(node->child[lr]), child, NULL_NORMAL, child, NULL_MARKED)) 
				return true;
		}
		else if (childStat == NULL_REPLACE) {
			int *currKeyPtr = node->keyPtr;
			if (DATA_ADDR(currKeyPtr) == DATA_ADDR(keyPtr) && DATA_STAT(currKeyPtr) == DNORMAL) {
				if (NODE_CAS(&(node->child[lr]), child, NULL_REPLACE, child, NULL_MARKED)) 
					return true;
			}
			else {
				return false;
			}
		}
	}
}

bool markAnyChild(Node *node, int lr, int status) {
	Node *child;
	int childStat;
	int tarStat;
	while(true) {
		child = node->child[lr];
		childStat = NODE_STATUS(child);
		if (childStat == NONNULL_MARKED || childStat == NULL_MARKED || childStat == NULL_PROMOTE || childStat == NONNULL_PROMOTE) {
			return true;
		}
		else {
			if (childStat == NONNULL_NORMAL && status == MARKED)
				tarStat = NONNULL_MARKED;
			else if (childStat == NONNULL_NORMAL && status == PROMOTE && lr == LEFT) 
				tarStat = NONNULL_PROMOTE;
			else if (childStat == NULL_NORMAL && status == PROMOTE && lr == LEFT)
				tarStat = NULL_PROMOTE;
			else
				tarStat = NULL_MARKED;
			if (NODE_CAS(&(node->child[lr]), child, childStat, child, tarStat))
				return true;
		}
	}
}

void markTreeNode(Node *node, int *keyPtr) {
	if(markNullChildOnly(node, LEFT, NULL_MARKED, keyPtr))
		markAnyChild(node, RIGHT, MARKED);
	else if(markNullChildOnly(node, RIGHT, NULL_MARKED, keyPtr))
		markAnyChild(node, LEFT, MARKED);
		
}



bool removeNode(Node *pred, Node *curr, int key) {
	Node *rp = curr->child[RIGHT];
	int rs = NODE_STATUS(rp);
	Node *lp = curr->child[LEFT];
	int ls = NODE_STATUS(lp);
	Node *ptr; int status;
	
	int *predKeyPtr = pred->keyPtr;
	int predKey = GETKEY(predKeyPtr);
	int lr = key > predKey ? RIGHT : LEFT;
	int predStat = NODE_STATUS(pred->child[lr]);

	if ((rs == NULL_MARKED || rs == NULL_PROMOTE) && (ls == NULL_MARKED || ls == NULL_PROMOTE)) {
		if (DATA_STAT(predKeyPtr) == DMARKED && lr == RIGHT) {
			ptr = curr, status = NULL_REPLACE;
		}	
		else
			ptr = curr, status = NULL_NORMAL;
	}
	else if (rs == NULL_MARKED || rs == NULL_PROMOTE) {
		ptr = GETADDR(lp), status = NONNULL_NORMAL;
	}
	else {
		ptr = GETADDR(rp), status = NONNULL_NORMAL;
	}

	if (predStat == NULL_NORMAL || predStat == NULL_MARKED || predStat == NULL_PROMOTE || predStat == NULL_REPLACE)
		return true;
	if (GETADDR(pred->child[lr]) != curr) {
		//printf("HERE %d %d %d %d\n", key, __LINE__, (uintptr_t)(pred->child[lr]), (uintptr_t)curr);
		return true;
	}
	else if (predStat == NONNULL_NORMAL) {
		if (NODE_CAS(&(pred->child[lr]), curr, NONNULL_NORMAL, ptr, status)) {
			if (status == NONNULL_NORMAL)
				ptr->bl = pred;
			return true;
		}
		else
			return removeNode(pred, curr, key);
	}
	else if (predStat == NONNULL_MARKED || (predStat == NONNULL_PROMOTE && lr == LEFT)) {
		if (isPresentInTree(pred)) {
			removeNode(pred->bl, pred, predKey);
		}
		else {
			curr->bl = pred->bl;
		}
		return removeNode(curr->bl, curr, key);
	}
	//printf("HERE %d %d %d %d\n", key, __LINE__, (uintptr_t)(pred->child[lr]), (uintptr_t)curr);
}

bool isZeroChildForDeletion(Node *node) {
	Node *rc = node->child[RIGHT];
	Node *lc = node->child[LEFT];
	int rs = NODE_STATUS(rc);
	int ls = NODE_STATUS(lc);
	if ((rs == NULL_MARKED || rs == NULL_PROMOTE) && (ls == NULL_MARKED || ls == NULL_PROMOTE))
		return true;
	return false;
}

bool removeTwoChild(Node *curr, int *currKeyPtr, int key, NodeLocation *nodeLoc) {
	Node *lp = curr->child[LEFT];
	if (ISNULL(lp))
		return removeTree(key, nodeLoc);
	Node *rp = curr->child[RIGHT];
	int rs = NODE_STATUS(rp);
	if (rs == NONNULL_NORMAL || (rs == NULL_REPLACE && DATA_STAT(curr->keyPtr) == DMARKED)) {
		if (rs == NONNULL_NORMAL) {
			if (isZeroChildForDeletion(GETADDR(rp))) {
				if (NODE_CAS(&(curr->child[RIGHT]), rp, NONNULL_NORMAL, rp, NULL_REPLACE)) {
				}
				else { 
					//printf("HERE : %d\n", __LINE__);
					return removeTree(key, nodeLoc);	
				}
			}
		}
		
		Node *succ = curr;
		Node *sr = curr->child[LEFT];
		bool sn = ISNULL(lp);
		
		while(true) {
			if (sn == true) {
				break;
			}
			succ = GETADDR(sr);
			sr = GETADDR(sr)->child[RIGHT];
			sn = ISNULL(sr);
		}
		
		int srStat = NODE_STATUS(sr);
		int *succKeyPtr = succ->keyPtr;
		int succKey = GETKEY(succKeyPtr);

		if (isInvalidSearch(curr, currKeyPtr))
			return false;
			
		if (srStat == NULL_MARKED) {
			markAnyChild(succ, LEFT, MARKED);
			removeNode(succ->bl, succ, succKey);
			return removeTwoChild(curr, currKeyPtr, key, nodeLoc);
		}
		else if (srStat == NULL_NORMAL) {
			if (DATA_STAT(succ->keyPtr) == DMARKED) {
				removeTree(succKey, nodeLoc);
				return removeTwoChild(curr, currKeyPtr, key, nodeLoc);
			}
			else if (NODE_CAS(&(succ->child[RIGHT]), sr, NULL_NORMAL, curr, NULL_PROMOTE)) {
				DCAS(&(curr->keyPtr), currKeyPtr, DMARKED, succKeyPtr, DNORMAL);
				markAnyChild(succ, LEFT, PROMOTE);
				int succLeftStat = NODE_STATUS(succ->child[LEFT]);
				if (succLeftStat == NULL_PROMOTE || succLeftStat == NONNULL_PROMOTE) {
					removeNode(succ->bl, succ, succKey);
					return true;
				}
				else {
					removeNode(succ->bl, succ, succKey);
					removeTree(succKey, nodeLoc);
					return true;
				}
			}
		}
		else if (srStat == NULL_PROMOTE) {
			if (GETADDR(sr) == curr && succKey != key) {
				DCAS(&(curr->keyPtr), currKeyPtr, DMARKED, succ->keyPtr, DNORMAL);
				markAnyChild(succ, LEFT, PROMOTE);
				int succLeftStat = NODE_STATUS(succ->child[LEFT]);
				if (succLeftStat == NULL_PROMOTE || succLeftStat == NONNULL_PROMOTE) {
					removeNode(succ->bl, succ, succKey);
					return true;
				}
				else {
					removeNode(succ->bl, succ, succKey);
					removeTree(succKey, nodeLoc);
					return true;
				} 
			}
			else {
				markAnyChild(succ, LEFT, MARKED);
				removeNode(succ->bl, succ, succKey);
				return removeTwoChild(curr, currKeyPtr, key, nodeLoc);
			}
		}
		else if (srStat == NULL_REPLACE) {
			if (DATA_STAT(succ->keyPtr) == DMARKED) {
				removeTwoChild(succ, succ->keyPtr, succKey, nodeLoc);
				return removeTwoChild(curr, currKeyPtr, key, nodeLoc);
			}
			else if (NODE_CAS(&(succ->child[RIGHT]), sr, NULL_REPLACE, curr, NULL_PROMOTE)) {
				DCAS(&(curr->keyPtr), currKeyPtr, DMARKED, succ->keyPtr, DNORMAL);
				markAnyChild(succ, LEFT, PROMOTE);
				int succLeftStat = NODE_STATUS(succ->child[LEFT]);
				if (succLeftStat == NULL_PROMOTE || succLeftStat == NONNULL_PROMOTE) {
					removeNode(succ->bl, succ, succKey);
					return true;
				}
				else {
					removeNode(succ->bl, succ, succKey);
					removeTree(succKey, nodeLoc);
					return true;
				}
			}
		}
		return removeTwoChild(curr, currKeyPtr, key, nodeLoc);
	}
	else {
		//printf("HERE : %d\n", __LINE__);
		return removeTree(key, nodeLoc);
	}
}

bool removeTree(int key, NodeLocation *nodeLoc) {
	find(key, nodeLoc, root, root, root->keyPtr);
	Node *pred = nodeLoc->pred;
	Node *curr = nodeLoc->curr;
	int currStat = NODE_STATUS(curr);
	if (currStat == NULL_NORMAL || currStat == NULL_MARKED || currStat == NULL_PROMOTE || currStat == NULL_REPLACE) {
		//printf("HERE : %d %d %d %d %d %d %d %d %d %d %d\n", key, __LINE__, (uintptr_t)(curr), (uintptr_t)(pred), (uintptr_t)(pred->child[RIGHT]), (uintptr_t)(pred->child[LEFT]), (uintptr_t)pred->bl, (uintptr_t)(GETADDR(curr)->bl), GETKEY(GETADDR(curr)->keyPtr), GETKEY(GETADDR(pred)->keyPtr), (uintptr_t)root);
		return false;
	}
	
	curr = GETADDR(curr);
	int *currKeyPtr = curr->keyPtr;
	int currKey = GETKEY(currKeyPtr);
	if (key != currKey && DATA_STAT(currKeyPtr) == DNORMAL) {
		//printf("HERE : %d %d\n", key, __LINE__);
		return false;
	}
	//printf("HERE : %d %d\n", key, __LINE__);
	markTreeNode(curr, currKeyPtr);

	Node *rp = curr->child[RIGHT];
	int rs = NODE_STATUS(rp);
	Node *lp = curr->child[LEFT];
	int ls = NODE_STATUS(lp);
	
	if ((rs == NULL_MARKED || rs == NONNULL_MARKED) && (ls == NULL_MARKED || ls == NONNULL_MARKED)) {
		return removeNode(pred, curr, key);
	}
	else if (rs == NONNULL_NORMAL && ls == NONNULL_NORMAL) {
		if (DCAS(&(curr->keyPtr), currKeyPtr, DNORMAL, currKeyPtr, DMARKED)) {
			//printf("HERE : %d %d\n", key, __LINE__);
			return removeTwoChild(curr, currKeyPtr, key, nodeLoc);
		}
		else if (DATA_STAT(currKeyPtr) == DMARKED) {
			//printf("HERE : %d %d\n", key, __LINE__);
			return removeTwoChild(curr, currKeyPtr, key, nodeLoc);
		}
		else { 
			//printf("HERE : %d\n", __LINE__);
			return removeTree(key, nodeLoc);
		}
	}
	else if (rs == NULL_PROMOTE && (ls == NONNULL_PROMOTE || ls == NULL_PROMOTE || ls == NULL_MARKED || ls == NONNULL_MARKED)) {
		removeNode(pred, curr, key);
		return removeTree(key, nodeLoc);
	}
	else if (rs == NULL_REPLACE && ls == NONNULL_NORMAL) {
		return removeTwoChild(curr, currKeyPtr, key, nodeLoc);
	}
	else {
		//printf("[ERROR] : %d %d %d\n", key, rs, ls);
		return removeTree(key, nodeLoc);
		return false;
	}
	return false;
}


bool searchTree(int key, NodeLocation *nodeLoc) {
	find(key, nodeLoc, root, root, root->keyPtr);
	Node *curr = nodeLoc->curr;
	bool n = ISNULL(curr);
	if (n == true) {
		return false;
	}
	else {
		int *currKeyPtr = GETADDR(curr)->keyPtr;
		int currKey = GETKEY(currKeyPtr);
		if (key == currKey)
			return true;
		return false;
	}
}

bool insertTree(int key, NodeLocation *nodeLoc) {
	find(key, nodeLoc, root, root, root->keyPtr);
	Node *pred = nodeLoc->pred;
	Node *curr = nodeLoc->curr;
	int predKey = GETKEY(pred->keyPtr);	
	int lr = key > predKey ? RIGHT : LEFT;
	bool n = ISNULL(curr);

	if (n == true) {
		int predStat = STATUS(pred->child[lr]);
		if (predStat == NORMAL || predStat == REPLACE) {
			Node *myNode = (Node *)malloc(sizeof(Node));
			myNode->keyPtr = (int *)malloc(sizeof(int));
			*(myNode->keyPtr) = key;
			myNode->child[LEFT] = (Node *)NULL_NORMAL;
			myNode->child[RIGHT] = (Node *)NULL_NORMAL;
			myNode->bl = pred;
			if (CAS(&(pred->child[lr]), curr, true, predStat, myNode, false, NORMAL)) {
				return true;
			}
			else 
				return insertTree(key, nodeLoc);
		}
		else if (predStat == MARKED || predStat == PROMOTE) {
			markAnyChild(pred, 1-lr, MARKED);
			removeNode(pred->bl, pred, predKey);
			return insertTree(key, nodeLoc);
		}
	}	
	else {
		int *currKeyPtr = GETADDR(curr)->keyPtr;
		int currKey = GETKEY(currKeyPtr);
		if (key != currKey) {
			return insertTree(key, nodeLoc);
		}
		else
			return false;
	} 
}

void printTree(Node *node) {
	if (ISNULL(node))
		return;
	printTree(GETADDR(node)->child[LEFT]);
	printf("[VARUN] %d\n", GETKEY(GETADDR(node)->keyPtr));
	//printf("[VARUN] %d %d %d %d %d %d %d %d\n", GETKEY(GETADDR(node)->keyPtr), NODE_STATUS(GETADDR(node)->child[LEFT]), NODE_STATUS(GETADDR(node)->child[LEFT]),  (int)((uintptr_t)GETADDR(node)->keyPtr & 0x01), ISNULL(GETADDR(node)->child[LEFT]), ISNULL(GETADDR(node)->child[RIGHT]), (uintptr_t)node, (uintptr_t)(GETADDR(node)->bl));
	printTree(GETADDR(node)->child[RIGHT]);
}

void testbench() {
	printf("Inside Testbench Method \n");
	NodeLocation *nodeLoc = (NodeLocation *)malloc(sizeof(NodeLocation));
	srand(time(NULL));
	const int numThreads = 1000;
	int arr[numThreads];
	
	std::vector<std::thread> remT(numThreads);
	std::vector<std::thread> insT(numThreads);
	for (int i = 0; i < numThreads; i++) { 
		do {
			arr[i] = rand();
		} while(arr[i] == INT_MAX);
	}
	NodeLocation **insLoc = (NodeLocation **)malloc(numThreads * sizeof(NodeLocation*));
	for(int i=0;i<numThreads;i++) {
		insLoc[i] = (NodeLocation *)malloc(sizeof(NodeLocation));
	}
	
	for(int i=0;i<numThreads;i++)
		insT[i] = std::thread(&insertTree, arr[i], insLoc[i]); 
	for(int i=0;i<numThreads;i++)
		insT[i].join(); 
	
//	for (int i = 0; i < numThreads; i++) 
//		insertTree(arr[i], nodeLoc);
	NodeLocation **remLoc = (NodeLocation **)malloc(numThreads * sizeof(NodeLocation*));
	for(int i=0;i<numThreads;i++) {
		remLoc[i] = (NodeLocation *)malloc(sizeof(NodeLocation));
	}
	
	for(int i=0;i<numThreads;i++)
		remT[i] = std::thread(&removeTree, arr[i], remLoc[i]); 
	for(int i=0;i<numThreads;i++)
		remT[i].join(); 
	printTree(root->child[LEFT]);
}



void *operateOnTree(void* tArgs)
{
  int chooseOperation;
  unsigned long lseed;
	unsigned long key;
  struct NodeLocation* tData = (struct NodeLocation*) tArgs;
  const gsl_rng_type* T;
  gsl_rng* r;
  gsl_rng_env_setup();
  T = gsl_rng_default;
  r = gsl_rng_alloc(T);
	lseed = tData->lseed;
  gsl_rng_set(r,lseed);

  while(!start)
  {
  }
	while(!steadyState)
	{
	  chooseOperation = gsl_rng_uniform(r)*100;
		key = gsl_rng_uniform_int(r,range) + 2;
    if(chooseOperation < searchPer)
    {
      searchTree(key, tData);
    }
    else if (chooseOperation < insertPer)
    {
      insertTree(key, tData);
    }
    else
    {
      removeTree(key, tData);
    }
	}
	
	tData->insertCount = 0;
	tData->deleteCount = 0;
	tData->searchCount = 0;
	while(!stop)
  {
    chooseOperation = gsl_rng_uniform(r)*100;
		key = gsl_rng_uniform_int(r,range); 
    if (chooseOperation < searchPer)
    {
			tData->searchCount++;
      searchTree(key, tData);
    }
    else if (chooseOperation < insertPer)
    {
      	insertTree(key, tData);
			tData->insertCount++;
    }
    else
    {
      removeTree(key, tData);
		tData->deleteCount++;
    }
  }
  return NULL;
} 

int main(int argc, char **argv) {
	root->keyPtr = (int *)malloc(sizeof(int));
	*(root->keyPtr) = INT_MAX;
	root->child[LEFT] = (Node *)0x04;
	root->child[RIGHT] = (Node *)0x04;
	root->bl = root;
	//testbenchSyncro();
/*	struct timespec runTime, transientTime;
	unsigned long lseed;
	numThreads = atoi(argv[1]);
	searchPer = atoi(argv[2]);
	insertPer = searchPer + atoi(argv[3]);
	removePer = insertPer + atoi(argv[4]);

	runTime.tv_sec = atoi(argv[5]);
	runTime.tv_nsec = 0;
	transientTime.tv_sec = 0;
	transientTime.tv_nsec = 2000000;

	range = (unsigned long) atol(argv[6]) - 1;
	lseed = (unsigned long)atol(argv[7]);

  const gsl_rng_type* T;
  gsl_rng* r;
  gsl_rng_env_setup();
  T = gsl_rng_default;
  r = gsl_rng_alloc(T);
  gsl_rng_set(r,lseed);
	//testbench();
	
	NodeLocation *initialInsertArgs = (NodeLocation *)malloc(sizeof(NodeLocation));
	initialInsertArgs->insertCount = 0;
	initialInsertArgs->deleteCount = 0;
	initialInsertArgs->searchCount = 0;
	
	int i = 0;
	while(i < range/2) {
		if (insertTree(gsl_rng_uniform_int(r,range), initialInsertArgs))
			i++;
	}
	NodeLocation **tArgs = (struct NodeLocation**)malloc(numThreads * sizeof(struct NodeLocation*));
	for (int i = 0; i < numThreads; i++) {
		tArgs[i] = (struct NodeLocation *)malloc(sizeof(NodeLocation));
		tArgs[i]->tid = i;
		tArgs[i]->lseed = gsl_rng_get(r);
		tArgs[i]->insertCount = 0;
		tArgs[i]->deleteCount = 0;
		tArgs[i]->searchCount = 0;
	}
	pthread_t threadArray[numThreads];
	for(int i=0;i<numThreads;i++)
	{
		pthread_create(&threadArray[i], NULL, operateOnTree, (void*) tArgs[i] );
	}	
	printf("Starting Steady State\n");
		start=true; 										//start operations
	nanosleep(&transientTime,NULL); //warmup
	printf("Starting Experiment\n");
	steadyState=true;
	nanosleep(&runTime,NULL);
	stop=true;		
	printf("Finished\n");
	for(int i=0;i<numThreads;i++)
		pthread_join(threadArray[i], NULL);

	unsigned long totalInsertCount = 0;
	unsigned long totalRemoveCount = 0;
	unsigned long totalSearchCount = 0;
	for(int i=0;i<numThreads;i++) {
		totalInsertCount += tArgs[i]->insertCount;
		totalRemoveCount += tArgs[i]->deleteCount;
		totalSearchCount += tArgs[i]->searchCount;
	}
	unsigned long totalOperations = totalSearchCount + totalInsertCount + totalRemoveCount;
	double MOPS = totalOperations/(runTime.tv_sec*1000000.0);
	printf("Through Put is : %f\n", MOPS);*/ 
	testbench();
	return 0;
}
