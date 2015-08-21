#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <stdint.h> 
#include <time.h>
//#include <pthread.h>
#include <vector>
#include <thread>

const int LEFT = 0, RIGHT  = 1;
const int NORMAL = 0, MARKED = 1, PROMOTE = 2, REPLACE = 3;
const int DNORMAL = 0, DMARKED = 1;

#define ISNULL(node) (bool)((uintptr_t)node & 0x04)
#define GETADDR(node) ((Node *)((uintptr_t)node & ~0x07))
#define GETKEY(ptr) (*(int *)((uintptr_t)(ptr) & ~0x01))
#define STATUS(node) (int)((uintptr_t)node & 0x03) 
#define markNode(node, null, status) \
	(((uintptr_t)node & ~0x07) | (null << 2) | status) 
#define CAS(ptr, s, sn, ss, t, tn, ts) \
	__sync_bool_compare_and_swap(ptr, markNode(s, sn, ss), markNode(t, tn, ts))
#define DCAS(ptr, s, ss, t, ts) \
	__sync_bool_compare_and_swap(ptr, (((uintptr_t)s & ~0x01) | ss), (((uintptr_t)t & ~0x01) | ts)) 

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
	
	NodeLocation(Node *ancNode, Node *pred, Node *curr, int *ancKeyPtr) {
		this->ancNode = ancNode;
		this->pred = pred;
		this->curr = curr;
		this->ancKeyPtr = ancKeyPtr;
	}
};

bool isInvalidSearch(Node *node, int *keyPtr) {
	int *nodeKeyPtr = (int *)((uintptr_t)(GETADDR(node)->keyPtr) & ~0x01);
	if (nodeKeyPtr != ((int *)((uintptr_t)keyPtr & ~0x01)))
		return true;
	return false;
}

bool removeTree(int, NodeLocation *); 

void find(int key, NodeLocation *nodeLoc, Node *startNode, Node *_ancNode, int *_ancKeyPtr) {
	Node *curr = startNode;
	Node *pred = curr->bl;
	Node *ancNode = ancNode;
	int *ancKeyPtr = ancKeyPtr, *currKeyPtr;
	bool n;	
	int currKey, lr;
	while(true) {
		n = ISNULL(curr);
		if (n == true) {
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

bool insert(int key, NodeLocation *nodeLoc) {
	find(key, nodeLoc, root, root, root->keyPtr);
	Node *pred = nodeLoc->pred;
	Node *curr = nodeLoc->curr;
	bool n = ISNULL(curr);
	if (n == true) {
		int predKey = GETKEY(GETADDR(pred)->keyPtr);
		Node *myNode = (Node *)malloc(sizeof(Node));
		myNode->keyPtr = (int *)malloc(sizeof(int));
		*(myNode->keyPtr) = key;
		myNode->child[LEFT] = (Node *)0x04;
		myNode->child[RIGHT] = (Node *)0x04;
		myNode->bl = pred;
		if (key > predKey)
			pred->child[RIGHT] = myNode;
		else
			pred->child[LEFT] = myNode;
	}
	else
		return false;
}

bool markChildNode(Node *node, int lr, int status, bool markNullOnly, int key) {
	while(true) {
		Node *curr = node->child[lr];
		int currStat = STATUS(curr);
		int n = ISNULL(curr);
		if (currStat == MARKED || currStat == PROMOTE)
			return true;
		else {
			if (n == true && markNullOnly == true) {
				if (currStat == NORMAL) {
					if (CAS(&(node->child[lr]), curr, true, NORMAL, curr, true, status)) {
						return true;
					}			
				}
				else if (currStat == REPLACE) {
					int *keyPtr = node->keyPtr;
					if (((uintptr_t)keyPtr & 0x01) == DMARKED) {
						return false;
					}
					else {
						if (CAS(&(node->child[lr]), curr, true, REPLACE, curr, n, status)) {
							return true;
						}			
					}
				}
			}
			else {
				if (currStat == NORMAL || currStat == REPLACE) {
					if (CAS(&(node->child[lr]), curr, n, currStat, curr, n, status)) {
						return true;
					}			
				}
			}
		}
	}
}

void markTreeNode(Node *node, int key) {
	if (markChildNode(node, LEFT, MARKED, true, key))
		markChildNode(node, RIGHT, MARKED, false, key);
	else if (markChildNode(node, RIGHT, MARKED, true, key))
		markChildNode(node, LEFT, MARKED, false, key);
}

bool isPresentInTree(Node *node) {
	Node *par = node->bl;
	Node *rc = (par->child[RIGHT]);
	Node *lc = (par->child[LEFT]);
	bool rn = ISNULL(rc);
	bool ln = ISNULL(lc);
	rc = GETADDR(rc);
	lc = GETADDR(lc);
	if ((rc == node && rn == false) || (lc == node && ln == false))
		return true;
	return false;
}

bool removeNode(Node *pred, Node *curr, int key) {
	Node *rp = curr->child[RIGHT];
	Node *lp = curr->child[LEFT];
	bool rn = ISNULL(rp);
	bool ln = ISNULL(lp);
	Node *ptr; int status; bool n;
	int *predKeyPtr = pred->keyPtr;
	int predKey = GETKEY(predKeyPtr);
	int predKeyStat = ((uintptr_t)predKeyPtr & 0x01);
	int lr = key > predKey ? RIGHT : LEFT;
	if (rn == true && ln == true) {
		if (lr == RIGHT && predKeyStat == DMARKED)
			ptr = curr, n = true, status = REPLACE;
		else
			ptr = curr, n = true, status = NORMAL;
	}
	else if (rn == true) {
		ptr = GETADDR(lp), n = false, status = NORMAL;
	}
	else {
		ptr = GETADDR(rp), n = false, status = NORMAL;
	}
	
	bool pn = ISNULL(pred->child[lr]);
	if (pn == true)
		return false;
	else {
		if (GETADDR(pred->child[lr]) == curr) {
			int predStat = STATUS(pred->child[lr]);
			if (predStat == NORMAL) {
				if (CAS(&(pred->child[lr]), curr, false, NORMAL, ptr, n, status)) {
					if (ptr != NULL)
						ptr->bl = pred;
					return true;
				}
				else
					return removeNode(pred, curr, key);
			}
			else if (predStat == MARKED || predStat == PROMOTE) {
				if (isPresentInTree(pred))
					removeNode(pred->bl, pred, predKey);
				else
					curr->bl = pred->bl;
				return removeNode(curr->bl, curr, key);
			}
		}
		return false;
	}
}

bool isZeroChildForDeletion(Node *node) {
	Node *rp = node->child[RIGHT];
	Node *lp = node->child[LEFT];
	bool rn = ISNULL(rp);
	bool ln = ISNULL(lp);
	int rs = STATUS(rp);
	int ls = STATUS(lp);
	if (rn && ln && rs != NORMAL && rs != REPLACE && ls != NORMAL)
		return true;
	return false;
}

bool removeTwoChild(Node *node, int *keyPtr, int key, NodeLocation *nodeLoc) {
	Node *lp = node->child[LEFT];
	bool ln = ISNULL(lp);
	if (ln == true)
		return removeTree(key, nodeLoc);
	Node *rp = node->child[RIGHT];
	bool rn = ISNULL(rp);
	int rs = STATUS(rp);
	if (rn == false || (rs == REPLACE && rn == true)) {
		if (rn == false && isZeroChildForDeletion(GETADDR(rp))) {
			if (CAS(&(node->child[RIGHT]), rp, false, NORMAL, rp, true, REPLACE)) {
			}
			else 
				return removeTree(key, nodeLoc);
		}
		Node *succ = node;
		Node *sr = node->child[LEFT];
		bool sn = ISNULL(sr);
		while(true) {
			if (sn == true) {
				break;
			}
			succ = GETADDR(sr);
			sr = GETADDR(sr)->child[RIGHT];
			sn = ISNULL(sr);
		}
		int *succKeyPtr = succ->keyPtr;
		int succKey = GETKEY(succKeyPtr);
		int succStat = STATUS(sr);
		if (isInvalidSearch(node, keyPtr))
			return false;
		if (succStat == MARKED) {
			markChildNode(succ, LEFT, MARKED, true, succKey);
			removeNode(succ->bl, succ, succKey);
			return removeTwoChild(node, keyPtr, key, nodeLoc);
		}
		else if (succStat == NORMAL || succStat == REPLACE) {
			if (succStat == REPLACE && (((uintptr_t)succKeyPtr & 0x01) == DMARKED)) {
				removeTwoChild(succ, succKeyPtr, succKey, nodeLoc);
				return removeTwoChild(node, keyPtr, key, nodeLoc);
			}
			if (CAS(&(succ->child[RIGHT]), sr, true, NORMAL, sr, true, PROMOTE)) {
				DCAS(&(node->keyPtr), keyPtr, DMARKED, succKeyPtr, DNORMAL);
				markChildNode(succ, LEFT, PROMOTE, true, succKey);
				if (STATUS(succ->child[LEFT]) == PROMOTE) {
					removeNode(succ->bl, succ, succKey);
					return true;
				}
				removeNode(succ->bl, succ, succKey);
				removeTree(succKey, nodeLoc);
				return true;
			}
		}
		else if (succStat == PROMOTE) {
			if (key != succKey) {
				if (DCAS(&(node->keyPtr), keyPtr, DMARKED, succKeyPtr, DNORMAL)) {
					markChildNode(succ, LEFT, PROMOTE, true, succKey);
					if (STATUS(succ->child[LEFT]) == PROMOTE) {
						removeNode(succ->bl, succ, succKey);
						return true;
					}
					removeNode(succ->bl, succ, succKey);
					removeTree(succKey, nodeLoc);
					return true;
				}
				else {
					markChildNode(succ, LEFT, MARKED, true, succKey);
					removeNode(succ->bl, succ, succKey);
					return false;
				}
			}
			else {
				markChildNode(succ, LEFT, MARKED, true, succKey);
				removeNode(succ->bl, succ, succKey);
				return removeTwoChild(node, keyPtr, key, nodeLoc);
			}
		}
		return removeTwoChild(node, keyPtr, key, nodeLoc);
	}
	else 
		return removeTree(key, nodeLoc);
}

bool removeTree(int key, NodeLocation *nodeLoc) {
	find(key, nodeLoc, root, root, root->keyPtr);
	Node *pred = nodeLoc->pred;
	Node *curr = nodeLoc->curr;

	bool cn = ISNULL(curr);
	if (cn == true)
		return false;
	curr = GETADDR(curr);
	int *currKeyPtr	= curr->keyPtr;
	int currKey = GETKEY(currKeyPtr);
	if (key != currKey)
		return false;

	// Now, mark the node
	markTreeNode(curr, key);
	Node *rp = curr->child[RIGHT];
	Node *lp = curr->child[LEFT];
	int rs = STATUS(rp);
	int ls = STATUS(lp);
	if (rs == MARKED && ls == MARKED)
		return removeNode(pred, curr, key);
	else if (rs == NORMAL && ls == NORMAL) {
		 (DCAS(&(curr->keyPtr), currKeyPtr, DNORMAL, currKeyPtr, DMARKED)); 
			currKeyPtr = curr->keyPtr;
			return removeTwoChild(curr, currKeyPtr, key, nodeLoc);
		//}
	//	else {
	//		currKeyPtr = curr->keyPtr;
	//		if (((uintptr_t)currKeyPtr & 0x01) == DMARKED) {
	//			return removeTwoChild(curr, currKeyPtr, key, nodeLoc);
	//		}
	//		return false;
	//	}
	}
	else if (rs == REPLACE && ls == NORMAL) {
			currKeyPtr = curr->keyPtr;
		if (((uintptr_t)currKeyPtr & 0x01) == DMARKED)
			return removeTwoChild(curr, currKeyPtr, key, nodeLoc);
		return false;
	}
	else if (rs == PROMOTE && ls == PROMOTE) {
		removeNode(pred, curr, key);
		return removeTree(key, nodeLoc);
	}
	else if (rs == PROMOTE && ls == MARKED) {
		removeNode(pred, curr, key);
		return removeTree(key, nodeLoc);
	}
	return false;
}

void printTree(Node *node) {
	if (ISNULL(node))
		return;
	printTree(GETADDR(node)->child[LEFT]);
	printf("[VARUN] %d %d %d %d %d %d\n", GETKEY(GETADDR(node)->keyPtr), STATUS(GETADDR(node)->child[LEFT]), STATUS(GETADDR(node)->child[LEFT]),  (int)((uintptr_t)GETADDR(node)->keyPtr & 0x01), ISNULL(GETADDR(node)->child[LEFT]), ISNULL(GETADDR(node)->child[RIGHT]) );
	printTree(GETADDR(node)->child[RIGHT]);
}

void testbench() {
	printf("Inside Testbench Method \n");
	NodeLocation *nodeLoc = (NodeLocation *)malloc(sizeof(NodeLocation));
	srand(time(NULL));
	const int numThreads = 1000;
	int arr[numThreads];
  	//pthread_t remT[numThreads];
	std::vector<std::thread> remT(numThreads);
	for (int i = 0; i < numThreads; i++) { 
		do {
			arr[i] = rand();
		} while(arr[i] == INT_MAX);
	}
	for (int i = 0; i < numThreads; i++) 
		insert(arr[i], nodeLoc);
//	for (int i = 0; i < numThreads; i++) 
//		remove(arr[i], nodeLoc, root, root);
	NodeLocation **remLoc = (NodeLocation **)malloc(numThreads * sizeof(NodeLocation*));
	for(int i=0;i<numThreads;i++) {
		remLoc[i] = (NodeLocation *)malloc(sizeof(NodeLocation));
	}
	for(int i=0;i<numThreads;i++)
		remT[i] = std::thread(&removeTree, arr[i], remLoc[i]); 
		//pthread_create(&remT[i], NULL, removeTree, arr[i], remLoc[i], root, root);
	for(int i=0;i<numThreads;i++)
		remT[i].join(); 
		//pthread_join(remT[i], NULL);
	printTree(root->child[LEFT]);
}

int main(void) {
	root->keyPtr = (int *)malloc(sizeof(int));
	*(root->keyPtr) = INT_MAX;
	root->child[LEFT] = (Node *)0x04;
	root->child[RIGHT] = (Node *)0x04;
	testbench();
	return 0;
}
