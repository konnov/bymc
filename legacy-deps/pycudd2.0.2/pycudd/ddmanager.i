%{
#ifndef FROM_PYCUDDI
#error Use only from pycudd.i. Make sure to define FROM_PYCUDDI!
#endif
class CuddFatalError { 
public:
  CuddFatalError(string err);
  string er;
};
 
 CuddFatalError::CuddFatalError(string err) {
   er = err;
 }
   
%}
%{
void KillAllNodes(DdManager * self) {
#ifdef PYCUDD_DEBUG
  cerr << "Entering kill all nodes" << endl;
#endif
  int size;
  int i, j;
  int remain;	/* the expected number of remaining references to one */
  DdNodePtr *nodelist;
  DdNode *node;
  DdNode *Node;
  DdNode *sentinel = &(self->sentinel);
  DdSubtable *subtable;
  int count = 0;
  int badrefs = Cudd_CheckZeroRef(self);
  int collected = 0;
  int zeroed = 0;
  int ord, index;
  if (!badrefs) {
    cerr << "All nodes have already been disposed of correctly!" << endl;
    return;
  }
#ifdef PYCUDD_DEBUG
  cerr << badrefs << " uncollected nodes" << endl;
#endif
  /* First look at the BDD/ADD subtables. */
  remain = 1; /* reference from the manager */
  size = self->size;
  remain += 2 * size;	/* reference from the BDD projection functions */
  
  for (i = 0; i < size; i++) {
    subtable = &(self->subtables[i]);
    nodelist = subtable->nodelist;
    for (j = 0; (unsigned) j < subtable->slots; j++) {
      node = nodelist[j];
      while (node != sentinel) {
	if (node->ref != 0 && node->ref != DD_MAXREF) {
	  index = (int) node->index;
	  if (node != self->vars[index]) {
	    Node = Cudd_Regular(node);   // Do I need to do this? 
#ifdef PYCUDD_DEBUG
	    cerr << "Node: " << hex << node << " Refs: " << node->ref << endl;
#endif
	    Node->ref = 0; 
	    self->dead++;
	    ord = self->perm[Node->index];
	    self->subtables[ord].dead++;
	    zeroed++;
	  } else {
	    if (node->ref != 1) {
	      node->ref = 1;
	      zeroed++;      // Reducing a projection funcs refs to 1 preps it for killing
	    }
	  }  
	}
	node = node->next;
      }
    }
  }
  
  /* Then look at the ZDD subtables. */
  size = self->sizeZ;
  if (size) /* references from ZDD universe */
    remain += 2;
  
  for (i = 0; i < size; i++) {
    subtable = &(self->subtableZ[i]);
    nodelist = subtable->nodelist;
    for (j = 0; (unsigned) j < subtable->slots; j++) {
      node = nodelist[j];
      while (node != NULL) {
	if (node->ref != 0 && node->ref != DD_MAXREF) {
	  index = (int) node->index;
	  if (node == self->univ[self->permZ[index]]) {
	    if (node->ref > 2) {
	      node->ref = 2;   // Playing safe ... set it to values that CheckZeroRefs will feel happy about
	      zeroed++;
	    }
	  } else {
	    node->ref = 0;
	    zeroed++;
	    self->dead++;
	    ord = self->permZ[Node->index];
	    self->subtableZ[ord].dead++;
	  }
	}
	node = node->next;
      }
    }
  }
  
  /* Now examine the constant table. Plusinfinity, minusinfinity, and
  ** zero are referenced by the manager. One is referenced by the
  ** manager, by the ZDD universe, and by all projection functions.
  ** All other nodes should have no references.
  */
  
  nodelist = self->constants.nodelist;
  for (j = 0; (unsigned) j < self->constants.slots; j++) {
    node = nodelist[j];
    while (node != NULL) {
      if (node->ref != 0 && node->ref != DD_MAXREF) {
	if (node == self->one) {
	  node->ref = remain;
	} 
	else if (node == self->zero || node == self->plusinfinity || node == self->minusinfinity) {
	  if (node->ref != 1) {
	    node->ref = 1;
	  }
	} 
      }
      node = node->next;
    }
  }

  collected = cuddGarbageCollect(self, 1);
  mgr = NULL;
#ifdef PYCUDD_DEBUG
  cerr << "Exiting kill all nodes" << endl << "Zeroed refs for " << zeroed <<  " nodes.\nGarbage collection freed a total of " << collected << " nodes" << endl;
  assert(!Cudd_CheckZeroRef(self)); // Better be zero!!
#endif
}
%}

struct DdManager { };

%extend DdManager {
%feature("autodoc","1");
%pythoncode %{
  __doc__ = "This class wraps around the DdManager. The methods defined by this class provide themselves as the DdManager option (if needed). To use PyCUDD, you must have at least one DdManager instance and you must set DdManager.SetDefault before using any of the other functions. These functions are provided through ddmanager.i."
%}
%newobject DdManager;  DdManager(unsigned int numVars = 0, unsigned int numVarsZ = 0, unsigned int numSlots = CUDD_UNIQUE_SLOTS, unsigned int cacheSize = CUDD_CACHE_SLOTS, unsigned long maxMemory = 0) {
    DdManager* mgri = Cudd_Init(numVars,numVarsZ,numSlots,cacheSize,maxMemory);

    if (mgr) cerr << "Default manager already exists!" << endl;
    return mgri;
  }
  
  ~DdManager() {
#ifdef PYCUDD_DEBUG    
    cerr << "About to get rid of manager" << endl;
#endif
    int retval = Cudd_CheckZeroRef(self);
    if (!retval) {
      cerr << "Quitting manager" << endl;
    } else {
#ifdef PYCUDD_DEBUG
      cerr << retval << " unexpected non-zero reference counts" << endl;
#endif
#ifdef TESTING
      KillAllNodes(self);
#endif
    }
    Cudd_Quit(self);
    mgr = NULL;
  }

  // This takes a long int representing the address of a DdNode and 
  // derefs it. Use with caution!!
  void KillNode(long int num) {
#ifdef PYCUDD_DEBUG
    cerr << "Derefing " << hex << num << endl;
#endif PYCUDD_DEBUG
    Cudd_RecursiveDeref(self, (DdNode *) num);
  }

  /* CUDD Manager functions */

  /* Start wrapped by Aravind */
  int IsPsVar(int index) { return Cudd_bddIsPsVar(self, index); }
  int IsNsVar(int index) {  return Cudd_bddIsNsVar(self, index);  }  
  int SetPsVar(int index) { return Cudd_bddSetPsVar(self, index);  }  
  int SetNsVar(int index) { return Cudd_bddSetNsVar(self, index);  }  
  int SetPairIndex(int index, int pairIndex) { return Cudd_bddSetPairIndex(self,index,pairIndex);  }
  int ReadPairIndex(int index) { return Cudd_bddReadPairIndex(self,index); }
  int SetVarToBeGrouped(int index)  { return Cudd_bddSetVarToBeGrouped(self,index); }
  int SetVarHardGroup(int index)    { return Cudd_bddSetVarHardGroup(self,index); }
  int ResetVarToBeGrouped(int index){ return Cudd_bddResetVarToBeGrouped(self,index); }
  int IsVarToBeGrouped(int index)   { return Cudd_bddIsVarToBeGrouped(self,index); }
  int IsVarHardGroup(int index)     { return Cudd_bddIsVarHardGroup(self,index); }
  int SetVarToBeUngrouped (int index) { return Cudd_bddSetVarToBeUngrouped(self,index); }
  int IsVarToBeUngrouped  (int index) { return Cudd_bddIsVarToBeUngrouped(self,index); }
  int SetPiVar(int index) { return Cudd_bddSetPiVar(self,index); }
  int IsPiVar (int index) { return Cudd_bddIsPiVar(self,index); }
  int BindVar   (int index) { return Cudd_bddBindVar(self,index); }
  int UnbindVar (int index) { return Cudd_bddUnbindVar(self,index); }
  int VarIsBound (int index) { return Cudd_bddVarIsBound(self,index); }
  double ReadMaxGrowthAlternate() { return Cudd_ReadMaxGrowthAlternate(self); }
  void SetMaxGrowthAlternate (double mg) { Cudd_SetMaxGrowthAlternate(self,mg); }
  int ReadReorderingCycle () { return Cudd_ReadReorderingCycle(self); }
  void SetReorderingCycle (int cycle) { Cudd_SetReorderingCycle(self,cycle);}
  int PrintCover(DdNode *l, DdNode *u) { return Cudd_bddPrintCover(self, l, u); }
  unsigned int Prime(unsigned int p) { return Cudd_Prime(p); }
  int __len__() { return Cudd_ReadSize(self); }
%exception{
    try {
      $function
    } catch (CuddFatalError x) {
      PyErr_SetString(PyExc_RuntimeError,x.er.c_str());
      return NULL;
    }
}

  // Disallow all negative indices when using __getitem__
  %newobject __getitem__;
%newobject __getitem__;   DdNode * __getitem__(int i) { 
    if (i < 0) throw CuddFatalError("CUDD Fatal error: Negative argument to bddIthVar.");
    DdNode * result = Cudd_bddIthVar(self, i); 
    Cudd_Ref(result);
    return result; 
  }
  %exception;
  /* End wrapped by Aravind */  

%newobject addNewVar;  DdNode *  addNewVar() { DdNode* result = Cudd_addNewVar(self); Cudd_Ref(result); return result; }
%newobject addNewVarAtLevel;  DdNode *  addNewVarAtLevel( int level) { DdNode* result = Cudd_addNewVarAtLevel(self,  level); Cudd_Ref(result); return result; }
%newobject NewVar;  DdNode *  NewVar() { DdNode* result = Cudd_bddNewVar(self); Cudd_Ref(result); return result; }
%newobject NewVarAtLevel;  DdNode *  NewVarAtLevel( int level) { DdNode* result = Cudd_bddNewVarAtLevel(self,  level); Cudd_Ref(result); return result; }
%newobject addIthVar;  DdNode *  addIthVar( int i) { DdNode* result = Cudd_addIthVar(self,  i); Cudd_Ref(result); return result; }
%newobject IthVar;  DdNode *  IthVar( int i) { DdNode* result = Cudd_bddIthVar(self,  i); Cudd_Ref(result); return result; }
%newobject zddIthVar;  DdNode *  zddIthVar( int i) { DdNode* result = Cudd_zddIthVar(self,  i); Cudd_Ref(result); return result; }
  int  zddVarsFromBddVars( int multiplicity) { return Cudd_zddVarsFromBddVars(self,  multiplicity); }
%newobject addConst;  DdNode *  addConst( CUDD_VALUE_TYPE c) { DdNode* result = Cudd_addConst(self, c); Cudd_Ref(result); return result; } 
  void  AutodynEnable( int method) { Cudd_AutodynEnable(self, (Cudd_ReorderingType) method); }
  void  AutodynDisable() { Cudd_AutodynDisable(self); }
  %apply int * OUTPUT { int * dum_status };
  int  ReorderingStatus( int *dum_status) { return Cudd_ReorderingStatus(self, (Cudd_ReorderingType*) dum_status); } 
  void  AutodynEnableZdd( int method) { Cudd_AutodynEnableZdd(self, (Cudd_ReorderingType) method); }
  void  AutodynDisableZdd() { Cudd_AutodynDisableZdd(self); }
  int  ReorderingStatusZdd( int *dum_status) { return Cudd_ReorderingStatusZdd(self, (Cudd_ReorderingType*) dum_status); }
  %clear int * dum_status;
  int  zddRealignmentEnabled() { return Cudd_zddRealignmentEnabled(self); }
  void  zddRealignEnable() { Cudd_zddRealignEnable(self); }
  void  zddRealignDisable() { Cudd_zddRealignDisable(self); }
  int  RealignmentEnabled() { return Cudd_bddRealignmentEnabled(self); }
  void  RealignEnable() { Cudd_bddRealignEnable(self); }
  void  RealignDisable() { Cudd_bddRealignDisable(self); }
%newobject ReadOne;  DdNode *  ReadOne() { DdNode* result = Cudd_ReadOne(self); Cudd_Ref(result); return result; }
%newobject ReadZddOne;  DdNode *  ReadZddOne( int i) { DdNode* result = Cudd_ReadZddOne(self,  i); Cudd_Ref(result); return result; }
%newobject ReadZero;  DdNode *  ReadZero() { DdNode* result = Cudd_ReadZero(self); Cudd_Ref(result); return result; }
%newobject ReadLogicZero;  DdNode *  ReadLogicZero() { DdNode* result = Cudd_ReadLogicZero(self); Cudd_Ref(result); return result; }
%newobject ReadPlusInfinity;   DdNode *  ReadPlusInfinity() { DdNode* result = Cudd_ReadPlusInfinity(self); Cudd_Ref(result); return result; }
%newobject ReadMinusInfinity;   DdNode *  ReadMinusInfinity() { DdNode* result = Cudd_ReadMinusInfinity(self); Cudd_Ref(result); return result; }
%newobject ReadBackground;   DdNode *  ReadBackground() { DdNode* result = Cudd_ReadBackground(self); Cudd_Ref(result); return result; }
  unsigned int  ReadCacheSlots() { return Cudd_ReadCacheSlots(self); }
  double  ReadCacheUsedSlots() { return Cudd_ReadCacheUsedSlots(self); }
  double  ReadCacheLookUps() { return Cudd_ReadCacheLookUps(self); }
  double  ReadCacheHits() { return Cudd_ReadCacheHits(self); }
  double  ReadRecursiveCalls() { return Cudd_ReadRecursiveCalls(self); }
  unsigned int  ReadMinHit() { return Cudd_ReadMinHit(self); }
  void  SetMinHit( unsigned int hr) { Cudd_SetMinHit(self,   hr); }
  unsigned int  ReadLooseUpTo() { return Cudd_ReadLooseUpTo(self); }
  void  SetLooseUpTo( unsigned int lut) { Cudd_SetLooseUpTo(self,   lut); }
  unsigned int  ReadMaxCache() { return Cudd_ReadMaxCache(self); }
  unsigned int  ReadMaxCacheHard() { return Cudd_ReadMaxCacheHard(self); }
  void  SetMaxCacheHard( unsigned int mc) { Cudd_SetMaxCacheHard(self,   mc); }
  int  ReadSize() { return Cudd_ReadSize(self); }
  int  ReadZddSize() { return Cudd_ReadZddSize(self); }
  unsigned int  ReadSlots() { return Cudd_ReadSlots(self); }
  double  ReadUsedSlots() { return Cudd_ReadUsedSlots(self); }
  double  ExpectedUsedSlots() { return Cudd_ExpectedUsedSlots(self); }
  unsigned int  ReadKeys() { return Cudd_ReadKeys(self); }
  unsigned int  ReadDead() { return Cudd_ReadDead(self); }
  unsigned int  ReadMinDead() { return Cudd_ReadMinDead(self); }
  int  ReadReorderings() { return Cudd_ReadReorderings(self); }
  long  ReadReorderingTime() { return Cudd_ReadReorderingTime(self); }
  int  ReadGarbageCollections() { return Cudd_ReadGarbageCollections(self); }
  long  ReadGarbageCollectionTime() { return Cudd_ReadGarbageCollectionTime(self); }
  int GarbageCollect( int clearCache ) { return cuddGarbageCollect(self,clearCache); }
  double  ReadNodesFreed() { return Cudd_ReadNodesFreed(self); }
  double  ReadNodesDropped() { return Cudd_ReadNodesDropped(self); }
  double  ReadUniqueLookUps() { return Cudd_ReadUniqueLookUps(self); }
  double  ReadUniqueLinks() { return Cudd_ReadUniqueLinks(self); }
  int  ReadSiftMaxVar() { return Cudd_ReadSiftMaxVar(self); }
  void  SetSiftMaxVar( int smv) { Cudd_SetSiftMaxVar(self,  smv); }
  int  ReadSiftMaxSwap() { return Cudd_ReadSiftMaxSwap(self); }
  void  SetSiftMaxSwap( int sms) { Cudd_SetSiftMaxSwap(self,  sms); }
  double  ReadMaxGrowth() { return Cudd_ReadMaxGrowth(self); }
  void  SetMaxGrowth( double mg) { Cudd_SetMaxGrowth(self,  mg); }
  MtrNode *  ReadTree() { return Cudd_ReadTree(self); } 
  void  SetTree( MtrNode *tree) { Cudd_SetTree(self, tree); }
  void  FreeTree() { Cudd_FreeTree(self); }
  MtrNode *  ReadZddTree() { return Cudd_ReadZddTree(self); } 
  void  SetZddTree( MtrNode *tree) { Cudd_SetZddTree(self, tree); }
  void  FreeZddTree() { Cudd_FreeZddTree(self); }
  int  ReadPerm( int i) { return Cudd_ReadPerm(self,  i); }
  int  ReadPermZdd( int i) { return Cudd_ReadPermZdd(self,  i); }
  int  ReadInvPerm( int i) { return Cudd_ReadInvPerm(self,  i); }
  int  ReadInvPermZdd( int i) { return Cudd_ReadInvPermZdd(self,  i); }
%newobject ReadVars;   DdNode *  ReadVars( int i) { DdNode* result = Cudd_ReadVars(self,  i); Cudd_Ref(result); return result; }
  CUDD_VALUE_TYPE  ReadEpsilon() { return Cudd_ReadEpsilon(self); } 
  void  SetEpsilon( CUDD_VALUE_TYPE ep) { Cudd_SetEpsilon(self, ep); }
  Cudd_AggregationType  ReadGroupcheck() { return Cudd_ReadGroupcheck(self); }
  void  SetGroupcheck( Cudd_AggregationType gc) { Cudd_SetGroupcheck(self, gc); }
  int  GarbageCollectionEnabled() { return Cudd_GarbageCollectionEnabled(self); }
  void  EnableGarbageCollection() { Cudd_EnableGarbageCollection(self); }
  void  DisableGarbageCollection() { Cudd_DisableGarbageCollection(self); }
  int  DeadAreCounted() { return Cudd_DeadAreCounted(self); }
  void  TurnOnCountDead() { Cudd_TurnOnCountDead(self); }
  void  TurnOffCountDead() { Cudd_TurnOffCountDead(self); }
  int  ReadRecomb() { return Cudd_ReadRecomb(self); }
  void  SetRecomb( int recomb) { Cudd_SetRecomb(self,  recomb); }
  int  ReadSymmviolation() { return Cudd_ReadSymmviolation(self); }
  void  SetSymmviolation( int symmviolation) { Cudd_SetSymmviolation(self,  symmviolation); }
  int  ReadArcviolation() { return Cudd_ReadArcviolation(self); }
  void  SetArcviolation( int arcviolation) { Cudd_SetArcviolation(self,  arcviolation); }
  int  ReadPopulationSize() { return Cudd_ReadPopulationSize(self); }
  void  SetPopulationSize( int populationSize) { Cudd_SetPopulationSize(self,  populationSize); }
  int  ReadNumberXovers() { return Cudd_ReadNumberXovers(self); }
  void  SetNumberXovers( int numberXovers) { Cudd_SetNumberXovers(self,  numberXovers); }
  long  ReadMemoryInUse() { return Cudd_ReadMemoryInUse(self); }
  int  PrintInfo(FILE *fp) { return Cudd_PrintInfo(self, fp); } 
  long  ReadPeakNodeCount() { return Cudd_ReadPeakNodeCount(self); }
  int  ReadPeakLiveNodeCount() { return Cudd_ReadPeakLiveNodeCount(self); }
  long  ReadNodeCount() { return Cudd_ReadNodeCount(self); }
  long  zddReadNodeCount() { return Cudd_zddReadNodeCount(self); }
  int  EnableReorderingReporting() { return Cudd_EnableReorderingReporting(self); }
  int  DisableReorderingReporting() { return Cudd_DisableReorderingReporting(self); }
  int  ReorderingReporting() { return Cudd_ReorderingReporting(self); }
  Cudd_ErrorType  ReadErrorCode() { return Cudd_ReadErrorCode(self); }
  void  ClearErrorCode() { Cudd_ClearErrorCode(self); }
  FILE *  ReadStdout() { return Cudd_ReadStdout(self); }
  void  SetStdout( FILE *fp) { Cudd_SetStdout(self, fp); }
  FILE *  ReadStderr() { return Cudd_ReadStderr(self); } 
  void  SetStderr( FILE *fp) { Cudd_SetStderr(self, fp); }
  unsigned int  ReadNextReordering() { return Cudd_ReadNextReordering(self); }
  double  ReadSwapSteps() { return Cudd_ReadSwapSteps(self); }
  unsigned int  ReadMaxLive() { return Cudd_ReadMaxLive(self); }
  void  SetMaxLive( unsigned int maxLive) { Cudd_SetMaxLive(self,   maxLive); }
  long  ReadMaxMemory() { return Cudd_ReadMaxMemory(self); }
  void  SetMaxMemory( long maxMemory) { Cudd_SetMaxMemory(self,  maxMemory); }
  void  SetNextReordering( unsigned int next) { Cudd_SetNextReordering(self,   next); }
  int  DebugCheck() { return Cudd_DebugCheck(self); }
  int  CheckKeys() { return Cudd_CheckKeys(self); }
  MtrNode * MakeTreeNode( unsigned int low, unsigned int size, unsigned int type) { return Cudd_MakeTreeNode(self,   low,   size,   type); } 
  int  PrintLinear() { return Cudd_PrintLinear(self); }
  int  ReadLinear( int x, int y) { return Cudd_ReadLinear(self,  x,  y); }
  int  CheckZeroRef() { return Cudd_CheckZeroRef(self); }
  int  ReduceHeap( int heuristic, int minsize) { return Cudd_ReduceHeap(self, (Cudd_ReorderingType) heuristic,  minsize); }
  int  ShuffleHeap( IntArray *permutation) { return Cudd_ShuffleHeap(self,  permutation->vec); }  
  void  SymmProfile( int lower, int upper) { Cudd_SymmProfile(self,  lower,  upper); }
%newobject IndicesToCube;   DdNode *  IndicesToCube( IntArray *array, int n) { DdNode* result = Cudd_IndicesToCube(self,  array->vec,  n); Cudd_Ref(result); return result; } 
  double  AverageDistance() { return Cudd_AverageDistance(self); }
  MtrNode *  MakeZddTreeNode( unsigned int low, unsigned int size, unsigned int type) { return Cudd_MakeZddTreeNode(self,   low,   size,   type); } 
  void  zddPrintSubtable() { Cudd_zddPrintSubtable(self); }
  int  zddReduceHeap( int heuristic, int minsize) { return Cudd_zddReduceHeap(self, (Cudd_ReorderingType) heuristic,  minsize); }
  int  zddShuffleHeap( IntArray *permutation) { return Cudd_zddShuffleHeap(self,  permutation->vec); } 
  void  zddSymmProfile( int lower, int upper) { Cudd_zddSymmProfile(self,  lower,  upper); }
%newobject BddToAdd;   DdNode *  BddToAdd( DdNode *B) { DdNode* result = Cudd_BddToAdd(self,  B); Cudd_Ref(result); return result; }
%newobject addBddPattern;   DdNode *  addBddPattern( DdNode *f) { DdNode* result = Cudd_addBddPattern(self,  f); Cudd_Ref(result); return result; }
%newobject addBddThreshold;   DdNode *  addBddThreshold( DdNode *f, CUDD_VALUE_TYPE value) { DdNode* result = Cudd_addBddThreshold(self,  f, value); Cudd_Ref(result); return result; }
%newobject addBddStrictThreshold;   DdNode *  addBddStrictThreshold( DdNode *f, CUDD_VALUE_TYPE value) { DdNode* result = Cudd_addBddStrictThreshold(self,  f, value); Cudd_Ref(result); return result; }
%newobject addBddInterval;   DdNode *  addBddInterval( DdNode *f, CUDD_VALUE_TYPE lower, CUDD_VALUE_TYPE upper) { DdNode* result = Cudd_addBddInterval(self,  f, lower, upper); Cudd_Ref(result); return result; }
%newobject addBddIthBit;   DdNode *  addBddIthBit( DdNode *f, int bit) { DdNode* result = Cudd_addBddIthBit(self,  f,  bit); Cudd_Ref(result); return result; }
%newobject zddPortFromBdd;   DdNode *  zddPortFromBdd( DdNode *B) { DdNode* result = Cudd_zddPortFromBdd(self,  B); Cudd_Ref(result); return result; }
%newobject zddPortToBdd;   DdNode *  zddPortToBdd( DdNode *f) { DdNode* result = Cudd_zddPortToBdd(self,  f); Cudd_Ref(result); return result; }
%newobject MakeBddFromZddCover;   DdNode *  MakeBddFromZddCover( DdNode *node) { DdNode* result = Cudd_MakeBddFromZddCover(self,  node); Cudd_Ref(result); return result; }
  void PrintVersion(FILE *fp) { Cudd_PrintVersion(fp); }
  long Random() { return Cudd_Random(); }
  void Srandom( long seed) { Cudd_Srandom(seed); }
  void OutOfMem(long size) {  Cudd_OutOfMem(size); }
%newobject Transfer;   DdNode * Transfer( DdManager *ddDestination, DdNode *f) { DdNode* result = Cudd_bddTransfer(self, ddDestination, f); Cudd_Ref(result); return result; }
    
%newobject CubeArrayToBdd;   DdNode *  CubeArrayToBdd( IntArray *y) { DdNode* result = Cudd_CubeArrayToBdd(self, y->vec); Cudd_Ref(result); return result; }
  int  SetVarMap( DdArray *x, DdArray *y, int n) { return Cudd_SetVarMap(self,  x->vec,  y->vec,  n); }
%newobject ComputeCube;   DdNode *  ComputeCube( DdArray *vars, IntArray *phase, int n) { DdNode* result = Cudd_bddComputeCube(self,  vars->vec,  phase->vec,  n); Cudd_Ref(result); return result; }
  int  zddDumpDot( int n, DdArray *f, char **inames, char **onames, FILE *fp) { return Cudd_zddDumpDot(self,  n,  f->vec, inames, onames, fp); }
  int  DumpBlif( int n, DdArray *f, char **inames, char **onames, char *mname, FILE *fp, int mv) { return Cudd_DumpBlif(self,  n,  f->vec, inames, onames, mname, fp, mv); }
  int  DumpBlifBody( int n, DdArray *f, char **inames, char **onames, FILE *fp, int mv) { return Cudd_DumpBlifBody(self,  n,  f->vec, inames, onames, fp, mv); }
  int  DumpDot( int n, DdArray *f, char **inames, char **onames, FILE *fp) { return Cudd_DumpDot(self,  n,  f->vec,  inames,  onames, fp); }
  int  DumpDaVinci( int n, DdArray *f, char **inames, char **onames, FILE *fp) { return Cudd_DumpDaVinci(self,  n,  f->vec,  inames,  onames, fp); }
  int  DumpDDcal( int n, DdArray *f, char **inames, char **onames, FILE *fp) { return Cudd_DumpDDcal(self,  n,  f->vec,  inames,  onames, fp); }
  int  DumpFactoredForm( int n, DdArray *f, char **inames, char **onames, FILE *fp) { return Cudd_DumpFactoredForm(self,  n,  f->vec,  inames,  onames, fp); }

  /*  DDDmp Functions */
  int ArrayLoad( int rootmatchmode, char **rootmatchnames, int varmatchmode, char **varmatchnames, IntArray *varmatchauxids, IntArray *varcomposeids, int mode, char *filename, FILE *fp, DdArray *pproots) { return Dddmp_cuddBddArrayLoad( self, (Dddmp_RootMatchType) rootmatchmode, rootmatchnames, (Dddmp_VarMatchType) varmatchmode, varmatchnames, (int *) ( varmatchauxids ? varmatchauxids->vec : NULL), (int *) ( varcomposeids ? varcomposeids->vec : NULL), mode, filename, fp, &(pproots->vec)); }
  int ArrayStore( char *ddname, DdArray *roots, char **rootnames, char **varnames, IntArray *auxids, int mode, int varinfo, char *filename, FILE *fp) { return Dddmp_cuddBddArrayStore(self, ddname, roots->sz, roots->vec, rootnames, varnames, (int *) ( auxids ? auxids->vec : NULL), mode, (Dddmp_VarInfoType) varinfo, filename, fp); }
%newobject BddLoad;   DdNode *BddLoad( int varmatchmode, char **varmatchnames, IntArray *varmatchauxids, IntArray *varcomposeids, int mode, char *filename, FILE *fp) { return Dddmp_cuddBddLoad( self, (Dddmp_VarMatchType) varmatchmode, varmatchnames, (int *) ( varmatchauxids ? varmatchauxids->vec : NULL), (int *) ( varcomposeids ? varcomposeids->vec : NULL), mode, filename, fp); }
  int BddStore( char *ddname, DdNode *f, char **varnames, IntArray *auxids, int mode, int varinfo, char *fname, FILE *fp) { return Dddmp_cuddBddStore( self, ddname, f, varnames, (int *) (auxids ? auxids->vec : NULL), mode, (Dddmp_VarInfoType) varinfo, fname, fp); }
  int Bin2Text( char *filein, char *fileout) { return Dddmp_Bin2Text( filein, fileout); }
  int DisplayBinary( char *filein, char *fileout) { return Dddmp_cuddBddDisplayBinary( filein, fileout); }
  int Text2Bin( char *filein, char *fileout) { return Dddmp_Text2Bin( filein, fileout); }


  int  VectorSupportSize( DdArray *F, int n) { return Cudd_VectorSupportSize(self,  F->vec,  n); }
  int  ClassifySupport( DdNode *f, DdNode *g, DdArray *common, DdArray *onlyF, DdArray *onlyG) { return Cudd_ClassifySupport(self,  f,  g,  common->vec,  onlyF->vec,  onlyG->vec); }
%newobject Xgty;  DdNode *  Xgty( int N, DdArray *z, DdArray *x, DdArray *y) { DdNode* result = Cudd_Xgty(self,  N,  z->vec,  x->vec,  y->vec); Cudd_Ref(result); return result; }
%newobject Xeqy;  DdNode *  Xeqy( int N, DdArray *x, DdArray *y) { DdNode* result = Cudd_Xeqy(self,  N,  x->vec,  y->vec); Cudd_Ref(result); return result; }
%newobject Dxygtdxz;  DdNode *  Dxygtdxz( int N, DdArray *x, DdArray *y, DdArray *z) { DdNode* result = Cudd_Dxygtdxz(self,  N,  x->vec,  y->vec,  z->vec); Cudd_Ref(result); return result; }
%newobject Dxygtdyz;  DdNode *  Dxygtdyz( int N, DdArray *x, DdArray *y, DdArray *z) { DdNode* result = Cudd_Dxygtdyz(self,  N,  x->vec,  y->vec,  z->vec); Cudd_Ref(result); return result; }
  int SharingSize(DdArray *nodeArray, int n) { return Cudd_SharingSize(nodeArray->vec, n); }
  int ReadIndex(int i) { return Cudd_ReadPerm(self,  i); } 

  /* add code */
%newobject addPlus;   DdNode *  addPlus(DdArray *f, DdArray *g) { DdNode* result = Cudd_addPlus(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addTimes;   DdNode *  addTimes(DdArray *f, DdArray *g) { DdNode* result = Cudd_addTimes(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addThreshold;   DdNode *  addThreshold(DdArray *f, DdArray *g) { DdNode* result = Cudd_addThreshold(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addSetNZ;   DdNode *  addSetNZ(DdArray *f, DdArray *g) { DdNode* result = Cudd_addSetNZ(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addDivide;   DdNode *  addDivide(DdArray *f, DdArray *g) { DdNode* result = Cudd_addDivide(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addMinus;   DdNode *  addMinus(DdArray *f, DdArray *g) { DdNode* result = Cudd_addMinus(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addMinimum;   DdNode *  addMinimum(DdArray *f, DdArray *g) { DdNode* result = Cudd_addMinimum(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addMaximum;   DdNode *  addMaximum(DdArray *f, DdArray *g) { DdNode* result = Cudd_addMaximum(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addOneZeroMaximum;   DdNode *  addOneZeroMaximum(DdArray *f, DdArray *g) { DdNode* result = Cudd_addOneZeroMaximum(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addDiff;   DdNode *  addDiff(DdArray *f, DdArray *g) { DdNode* result = Cudd_addDiff(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addAgreement;   DdNode *  addAgreement(DdArray *f, DdArray *g) { DdNode* result = Cudd_addAgreement(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addOr;   DdNode *  addOr(DdArray *f, DdArray *g) { DdNode* result = Cudd_addOr(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addNand;   DdNode *  addNand(DdArray *f, DdArray *g) { DdNode* result = Cudd_addNand(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addNor;   DdNode *  addNor(DdArray *f, DdArray *g) { DdNode* result = Cudd_addNor(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addXor;   DdNode *  addXor(DdArray *f, DdArray *g) { DdNode* result = Cudd_addXor(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addXnor;   DdNode *  addXnor(DdArray *f, DdArray *g) { DdNode* result = Cudd_addXnor(self, f->vec,  g->vec); Cudd_Ref(result); return result; }
%newobject addWalsh;   DdNode *  addWalsh(DdArray *x, DdArray *y, int n) { DdNode* result = Cudd_addWalsh(self, x->vec,  y->vec,  n); Cudd_Ref(result); return result; }
%newobject addHamming;   DdNode *  addHamming(DdArray *xVars, DdArray *yVars, int nVars) { DdNode* result = Cudd_addHamming(self, xVars->vec,  yVars->vec,  nVars); Cudd_Ref(result); return result; }
%newobject addComputeCube;   DdNode *  addComputeCube(DdArray *vars, IntArray *phase, int n) { DdNode* result = Cudd_addComputeCube(self, vars->vec,  phase->vec,  n); Cudd_Ref(result); return result; }
%newobject addResidue;   DdNode * addResidue(int n, int m, int options, int top) { DdNode* result = Cudd_addResidue(self, n, m, options, top); Cudd_Ref(result); return result; }
%newobject addXeqy;   DdNode * addXeqy(int N, DdArray *x, DdArray *y) { DdNode* result = Cudd_addXeqy(self, N, x->vec, y->vec); Cudd_Ref(result); return result; }

  /* apa specific */
  int ApaNumberOfDigits(int binaryDigits) { return Cudd_ApaNumberOfDigits(binaryDigits); }
  DdApaNumber NewApaNumber(int digits) { return Cudd_NewApaNumber(digits); }
  void ApaCopy(int digits, DdApaNumber source, DdApaNumber dest) { return Cudd_ApaCopy(digits, source, dest); }
  DdApaDigit ApaAdd(int digits, DdApaNumber a, DdApaNumber b, DdApaNumber sum) { return Cudd_ApaAdd(digits, a, b, sum); }
  DdApaDigit ApaSubtract(int digits, DdApaNumber a, DdApaNumber b, DdApaNumber diff) { return Cudd_ApaSubtract(digits, a, b, diff); }
  DdApaDigit ApaShortDivision(int digits, DdApaNumber dividend, DdApaDigit divisor, DdApaNumber quotient) { return Cudd_ApaShortDivision(digits, dividend, divisor, quotient); }
  unsigned int ApaIntDivision(int  digits, DdApaNumber dividend, unsigned int  divisor, DdApaNumber  quotient) { return  Cudd_ApaIntDivision(digits, dividend, divisor, quotient); }
  void ApaShiftRight(int digits, DdApaDigit in, DdApaNumber a, DdApaNumber b) { Cudd_ApaShiftRight(digits, in, a, b); }
  void ApaSetToLiteral(int digits, DdApaNumber number, DdApaDigit literal) { Cudd_ApaSetToLiteral(digits, number, literal); }
  void ApaPowerOfTwo(int digits, DdApaNumber number, int power) { Cudd_ApaPowerOfTwo(digits, number, power); }
  int ApaCompare(int digitsFirst, DdApaNumber  first, int digitsSecond, DdApaNumber  second) { return  Cudd_ApaCompare(digitsFirst, first, digitsSecond, second); }
  int ApaCompareRatios(int digitsFirst, DdApaNumber firstNum, unsigned int firstDen, int digitsSecond, DdApaNumber secondNum, unsigned int secondDen) { return Cudd_ApaCompareRatios(digitsFirst, firstNum, firstDen, digitsSecond, secondNum, secondDen); }
  int ApaPrintHex(FILE *fp, int digits, DdApaNumber number) { return Cudd_ApaPrintHex(fp, digits, number); }
  int ApaPrintDecimal(FILE *fp, int digits, DdApaNumber number) { return Cudd_ApaPrintDecimal(fp, digits, number); }
  int ApaPrintExponential(FILE * fp, int  digits, DdApaNumber  number, int precision) { return Cudd_ApaPrintExponential(fp, digits, number, precision); }

  /* Added to DdManager */
  DdNode* One() {
    DdNode *result = Cudd_ReadOne(self);
    Cudd_Ref(result);
    return result;
  }

  DdNode* Zero() {
    DdNode *result = Cudd_ReadLogicZero(self);
    Cudd_Ref(result);
    return result;
  }

  int Sort (DdNode* leftnd, DdNode* rightnd) {
    return (Cudd_ReadPerm(self,Cudd_NodeReadIndex(rightnd)) - Cudd_ReadPerm(self,Cudd_NodeReadIndex(leftnd)));
  }
  int  PrintStdOut() { return Cudd_PrintInfo(self, stdout); } 
  
  DdNode* StateCube( char* cube, int base, int offset, int scale ) {
  	DdNode *tmp;
	int length;
	int i;
	DdNode *result = Cudd_ReadOne(self);
	Cudd_Ref(result);

	length = strlen(cube);

	for (i = length; i>=0; i--) {
	  if (cube[i]=='1') {
	    tmp = Cudd_bddAnd(self,result,Cudd_bddIthVar(self,((i*scale)+offset+base)));
	    Cudd_Ref(tmp);
	    Cudd_RecursiveDeref(self,result);
	    result = tmp;
	  } else if (cube[i]=='0') {
	    tmp = Cudd_bddAnd(self,result,Cudd_Not(Cudd_bddIthVar(self,((i*scale)+offset+base))));
	    Cudd_Ref(tmp);
	    Cudd_RecursiveDeref(self,result);
	    result = tmp;
	  }
	}
	return result;
  }

  void SetDefault() {
    mgr = self;
  }
};
