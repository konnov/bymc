////////////////////////////////////
//
// Wrapper for functions that naturally appear as methods of DdNode
//
////////////////////////////////////

%{
#ifndef FROM_PYCUDDI
#error Use only from pycudd.i. Make sure to define FROM_PYCUDDI!
#endif
%}

struct DdNode { };
%extend DdNode {
%feature("autodoc","1");
%pythoncode %{
def __iter__(self):
  global iter_meth, cudd_version
  if iter_meth == 0:
    return ForeachCubeIterator(self)
  elif iter_meth == 1:
    return ForeachNodeIterator(self)
  elif iter_meth == 2:
    if cudd_version < 0x020400:
      print "Cannot iterate over primes with CUDD < 2.4.0"
      raise RuntimeError
    npair = NodePair(self,self)
    return ForeachPrimeIterator(npair)
def __deepcopy__(self,memo):
  return self
__doc__ = "This class wraps around the basic DdNode. The methods defined by this class take the default manager as their DdManager option (if needed) and provide themselves as the first DdNode option that those functions require, as indicated by the self argument. These functions may be found in ddnode.i."
%}

  DdNode() {
   return NULL;
  }

  ~DdNode() {
    //cerr << "Deleting ddnode" << endl;
    if (mgr) {
      Cudd_RecursiveDeref(mgr,self);
    }
#ifdef PYCUDD_DEBUG
    else {
      cerr << "DdNode " << hex << self << " is alive after DdManager has quit!" << endl;
    }
#endif
  }
  /* Generator stuff -- added by Aravind */
  /* For all the funcs FirstXXX, NextXXX, return value is 1 if a valid node came out, 0 if not             */
  /* This value can be used to determine whether to raise a StopIteration exception or not (cf. dditer.py) */   
  /* Typemap and global magic is used to return the DdNode/cube represented as ints                        */
  /* A global variable XXX_iter is used to store the pointer that the generator returns to us. Note that we*/
  /* don't need to malloc the DdNode or ints, but we do malloc and extern the DdNode** and int**           */
  /* The typemaps defined in utils.i  point CUDD to use these globals, and return the values put there     */

  int FirstCube(DdGen *gen, int **dum_cube) {
    if (Cudd_IsGenEmpty(gen)) { /* Happens if you call the generator on Logic Zero */ return 0; }
    return 1;
  }
  
  int NextCube(DdGen *gen, int **dum_cube) {
    CUDD_VALUE_TYPE val;
    int tmp;
    if (!gen) { /* Something is seriously wrong ! */ assert(0); }
    if (Cudd_IsGenEmpty(gen)) { // We should never hit this -- raise StopIteration in python earlier.
      fprintf(Cudd_ReadStdout(mgr),"You shouldn\'t be here! Fix your Python iterator.");
      return 0;
    }
    else { // Have a cube to return
      tmp = Cudd_NextCube(gen, dum_cube, &val);
      if (tmp <= 0) { // The freakin' generator is already empty ...
	assert(Cudd_IsGenEmpty(gen));
	return 0;
      }
      return 1;
    }
  }
    
  int FirstNode(DdGen *gen, DdNode **dum_y) {
    if (Cudd_IsGenEmpty(gen)) { /* Happens if you call the generator on Logic Zero */ return 0; }
    return 1;
  }

  int NextNode(DdGen *gen, DdNode **dum_y) {
    int tmp;
    if (!gen) { /* Something is seriously wrong ! */ assert(gen); }
    if (Cudd_IsGenEmpty(gen)) { // We should never hit this -- raise StopIteration in python earlier.
      fprintf(Cudd_ReadStdout(mgr),"You shouldn\'t be here! Fix your Python iterator.\n");
      return 0;
    }
    else { // Have a cube to return
      tmp = Cudd_NextNode(gen, dum_y);
      if (tmp <= 0) { // The freakin' generator is already empty ...
	assert(Cudd_IsGenEmpty(gen));
	return 0;
      }
      return 1;
    } 
  } // NextNode

#if CUDDVER >= 0x020400
%newobject AndAbstractLimit;  DdNode * AndAbstractLimit(DdNode *g, DdNode *cube, unsigned int limit) { DdNode* result = Cudd_bddAndAbstractLimit(mgr, self,g,cube,limit); Cudd_Ref(result); return result; }
%newobject AndLimit;  DdNode * AndLimit(DdNode *g, unsigned int limit) { DdNode* result = Cudd_bddAndLimit(mgr, self, g, limit); Cudd_Ref(result); return result; }
%newobject NPAnd;  DdNode * NPAnd(DdNode *c) { DdNode* result =  Cudd_bddNPAnd(mgr, self, c); Cudd_Ref(result); return result; }
  DdTlcInfo * FindTwoLiteralClauses() { DdTlcInfo * result = Cudd_FindTwoLiteralClauses(mgr, self); return result; }
#endif
  int EpdCountMinterm(int nvars, EpDouble *epd) { return Cudd_EpdCountMinterm(mgr,self,nvars,epd); }
  // Added in this version of pycudd -- various decomposition techniques and other odds and ends
  int ApproxConjDecomp(DdNode ***dum_juncts) { return Cudd_bddApproxConjDecomp(mgr, self, dum_juncts); }
  int ApproxDisjDecomp(DdNode ***dum_juncts) { return Cudd_bddApproxDisjDecomp(mgr, self, dum_juncts); }
  int IterConjDecomp(DdNode ***dum_juncts) { return Cudd_bddIterConjDecomp(mgr, self, dum_juncts); } 
  int IterDisjDecomp(DdNode ***dum_juncts) { return Cudd_bddIterDisjDecomp(mgr, self, dum_juncts); }
  int GenConjDecomp(DdNode ***dum_juncts) { return Cudd_bddGenConjDecomp(mgr, self, dum_juncts); }
  int GenDisjDecomp(DdNode ***dum_juncts) { return Cudd_bddGenDisjDecomp(mgr, self, dum_juncts); }
  int VarConjDecomp(DdNode ***dum_juncts) { return Cudd_bddVarConjDecomp(mgr, self, dum_juncts); }
  int VarDisjDecomp(DdNode ***dum_juncts) { return Cudd_bddVarDisjDecomp(mgr, self, dum_juncts); }
  %apply int * OUTPUT { int * dum_distance };
%newobject ClosestCube;  DdNode * ClosestCube (DdNode *g, int *dum_distance) { DdNode* result = Cudd_bddClosestCube(mgr,self,g,dum_distance); Cudd_Ref(result); return result; }
  int LeqUnless (DdNode *g, DdNode *D) { return Cudd_bddLeqUnless (mgr,self,g,D); }
%newobject MakePrime;  DdNode * MakePrime (DdNode *f) { DdNode *result = Cudd_bddMakePrime (mgr,self,f); Cudd_Ref(result); return result; }
  double CountPathsToNonZero() { return  Cudd_CountPathsToNonZero(self); }
  int SupportIndex(int **dum_sup) { 
    *dum_sup = Cudd_SupportIndex(mgr,self);
    if (*dum_sup == NULL) return 0;
    else return 1;
  }
  // Existing pycudd wrappers
%newobject ExistAbstract;  DdNode *  ExistAbstract( DdNode *cube) { DdNode* result = Cudd_bddExistAbstract(mgr, self,  cube); Cudd_Ref(result); return result; }
%newobject XorExistAbstract;  DdNode *  XorExistAbstract( DdNode *g, DdNode *cube) { DdNode* result = Cudd_bddXorExistAbstract(mgr, self,  g,  cube); Cudd_Ref(result); return result; }
%newobject UnivAbstract;  DdNode *  UnivAbstract( DdNode *cube) { DdNode* result = Cudd_bddUnivAbstract(mgr, self,  cube); Cudd_Ref(result); return result; }
%newobject BooleanDiff;  DdNode *  BooleanDiff( int x) { DdNode* result = Cudd_bddBooleanDiff(mgr, self,  x); Cudd_Ref(result); return result; }
%newobject AndAbstract;  DdNode *  AndAbstract( DdNode *g, DdNode *cube) { DdNode* result = Cudd_bddAndAbstract(mgr, self,  g,  cube); Cudd_Ref(result); return result; }
  int  VarIsDependent( DdNode *var) { return Cudd_bddVarIsDependent(mgr, self,  var); }
  double  Correlation( DdNode *g) { return Cudd_bddCorrelation(mgr, self,  g); }
  double  CorrelationWeights( DdNode *g, DoubleArray *prob) { return Cudd_bddCorrelationWeights(mgr, self,  g,  prob->vec); }
%newobject Ite;  DdNode *  Ite( DdNode *g, DdNode *h) { DdNode* result = Cudd_bddIte(mgr, self,  g,  h); Cudd_Ref(result); return result; }
%newobject IteConstant; DdNode *  IteConstant( DdNode *g, DdNode *h) { DdNode* result = Cudd_bddIteConstant(mgr, self,  g,  h); Cudd_Ref(result); return result; }
%newobject Intersect;  DdNode *  Intersect( DdNode *g) { DdNode* result = Cudd_bddIntersect(mgr, self,  g); Cudd_Ref(result); return result; }
  int  FIntersect( DdNode *g) { int result = Cudd_bddLeq( mgr, self, Cudd_Not(g)) ? 0:1; return result; }

%newobject And;  DdNode *  And( DdNode *g) { DdNode* result = Cudd_bddAnd(mgr, self,  g); Cudd_Ref(result); return result; }
%newobject Or;  DdNode *  Or( DdNode *g) { DdNode* result = Cudd_bddOr(mgr, self,  g); Cudd_Ref(result); return result; }
%newobject Nand;  DdNode *  Nand( DdNode *g) { DdNode* result = Cudd_bddNand(mgr, self,  g); Cudd_Ref(result); return result; }
%newobject Nor;  DdNode *  Nor( DdNode *g) { DdNode* result = Cudd_bddNor(mgr, self,  g); Cudd_Ref(result); return result; }
%newobject Xor;  DdNode *  Xor( DdNode *g) { DdNode* result = Cudd_bddXor(mgr, self,  g); Cudd_Ref(result); return result; }
%newobject Xnor;  DdNode *  Xnor( DdNode *g) { DdNode* result = Cudd_bddXnor(mgr, self,  g); Cudd_Ref(result); return result; }
%newobject ClippingAnd;  DdNode *  ClippingAnd( DdNode *g, int maxDepth, int direction) { DdNode* result = Cudd_bddClippingAnd(mgr, self,  g,  maxDepth,  direction); Cudd_Ref(result); return result; }
%newobject ClippingAndAbstract;   DdNode *  ClippingAndAbstract( DdNode *g, DdNode *cube, int maxDepth, int direction) { DdNode* result = Cudd_bddClippingAndAbstract(mgr, self,  g,  cube,  maxDepth,  direction); Cudd_Ref(result); return result; }
%newobject LICompaction;   DdNode *  LICompaction( DdNode *c) { DdNode* result = Cudd_bddLICompaction(mgr, self,  c); Cudd_Ref(result); return result; }
%newobject Squeeze;   DdNode *  Squeeze( DdNode *u) { DdNode* result = Cudd_bddSqueeze(mgr, self,  u); Cudd_Ref(result); return result; }
%newobject Minimize;   DdNode *  Minimize( DdNode *c) { DdNode* result = Cudd_bddMinimize(mgr, self,  c); Cudd_Ref(result); return result; }
%newobject Constrain;   DdNode *  Constrain( DdNode *c) { DdNode* result = Cudd_bddConstrain(mgr, self,  c); Cudd_Ref(result); return result; }
%newobject Restrict;   DdNode *  Restrict( DdNode *c) { DdNode* result = Cudd_bddRestrict(mgr, self,  c); Cudd_Ref(result); return result; }
  int  PickOneCube( char *string) { return Cudd_bddPickOneCube(mgr, self, string); }
%newobject PickOneMinterm;  DdNode *  PickOneMinterm( DdArray *vars, int n) { DdNode* result = Cudd_bddPickOneMinterm(mgr, self,  vars->vec,  n); Cudd_Ref(result); return result; }
  DdArray *  PickArbitraryMinterms( DdArray *vars, int n, int k) { DdNode** tresult = Cudd_bddPickArbitraryMinterms(mgr, self,  vars->vec,  n,  k); DdArray* result = new DdArray(k); result->Assign(tresult, k); return result; } 
%newobject Compose;  DdNode *  Compose( DdNode *g, int v) { DdNode* result = Cudd_bddCompose(mgr, self,  g,  v); Cudd_Ref(result); return result; }
%newobject Permute;   DdNode *  Permute( IntArray *permut) { DdNode* result = Cudd_bddPermute(mgr, self,  permut->vec); Cudd_Ref(result); return result; }
%newobject VarMap;   DdNode *  VarMap() { DdNode* result = Cudd_bddVarMap(mgr, self); Cudd_Ref(result); return result; }
%newobject LiteralSetIntersection;   DdNode *  LiteralSetIntersection( DdNode *g) { DdNode* result = Cudd_bddLiteralSetIntersection(mgr, self,  g); Cudd_Ref(result); return result; }
  int  IsVarEssential( int id, int phase) { return Cudd_bddIsVarEssential(mgr, self,  id,  phase); }
  bool  Leq( DdNode *g) { return Cudd_bddLeq(mgr, self,  g) ? TRUE : FALSE; }
  DdArray *  CharToVect() { DdNode** tresult = Cudd_bddCharToVect(mgr, self); int size = Cudd_ReadSize(mgr); DdArray* result = new DdArray(size); result->Assign(tresult,size); return result; } 
  DdArray *  ConstrainDecomp() { DdNode** tresult = Cudd_bddConstrainDecomp(mgr, self); int size = Cudd_ReadSize(mgr); DdArray* result = new DdArray(size); result->Assign(tresult,size); return result; } 
%newobject Isop;   DdNode *  Isop( DdNode *U) { DdNode* result = Cudd_bddIsop(mgr, self,  U); Cudd_Ref(result); return result; }
%newobject SwapVariables;   DdNode *  SwapVariables( DdArray *x, DdArray *y, int n) { DdNode* result = Cudd_bddSwapVariables(mgr, self,  x->vec,  y->vec,  n); Cudd_Ref(result); return result; }
%newobject AdjPermuteX;   DdNode *  AdjPermuteX( DdArray *x, int n) { DdNode* result = Cudd_bddAdjPermuteX(mgr, self,  x->vec,  n); Cudd_Ref(result); return result; }
%newobject VectorCompose;   DdNode *  VectorCompose( DdArray *vector) { DdNode* result = Cudd_bddVectorCompose(mgr, self,  vector->vec); Cudd_Ref(result); return result; }
  void  SetBackground() { Cudd_SetBackground(mgr, self); }
%newobject UnderApprox;   DdNode *  UnderApprox( int numVars, int threshold, int safe, double quality) { DdNode* result = Cudd_UnderApprox(mgr, self,  numVars,  threshold,  safe,  quality); Cudd_Ref(result); return result; }
%newobject OverApprox;   DdNode *  OverApprox( int numVars, int threshold, int safe, double quality) { DdNode* result = Cudd_OverApprox(mgr, self,  numVars,  threshold,  safe,  quality); Cudd_Ref(result); return result; }
%newobject RemapUnderApprox;   DdNode *  RemapUnderApprox( int numVars, int threshold, double quality) { DdNode* result = Cudd_RemapUnderApprox(mgr, self,  numVars,  threshold,  quality); Cudd_Ref(result); return result; }
%newobject RemapOverApprox;   DdNode *  RemapOverApprox( int numVars, int threshold, double quality) { DdNode* result = Cudd_RemapOverApprox(mgr, self,  numVars,  threshold,  quality); Cudd_Ref(result); return result; }
%newobject BiasedUnderApprox;   DdNode *  BiasedUnderApprox( DdNode *b, int numVars, int threshold, double quality1, double quality0) { DdNode* result = Cudd_BiasedUnderApprox(mgr, self,  b,  numVars,  threshold,  quality1,  quality0); Cudd_Ref(result); return result; }
%newobject BiasedOverApprox;   DdNode *  BiasedOverApprox( DdNode *b, int numVars, int threshold, double quality1, double quality0) { DdNode* result = Cudd_BiasedOverApprox(mgr, self,  b,  numVars,  threshold,  quality1,  quality0); Cudd_Ref(result); return result; }
%newobject Cofactor;  DdNode *  Cofactor( DdNode *g) { DdNode* result = Cudd_Cofactor(mgr, self,  g); Cudd_Ref(result); return result; }
%newobject FindEssential;   DdNode *  FindEssential() { DdNode* result = Cudd_FindEssential(mgr, self); Cudd_Ref(result); return result; }
%newobject SubsetCompress;   DdNode *  SubsetCompress( int nvars, int threshold) { DdNode* result = Cudd_SubsetCompress(mgr, self,  nvars,  threshold); Cudd_Ref(result); return result; }
%newobject SupersetCompress;   DdNode *  SupersetCompress( int nvars, int threshold) { DdNode* result = Cudd_SupersetCompress(mgr, self,  nvars,  threshold); Cudd_Ref(result); return result; }
%newobject CProjection;   DdNode *  CProjection( DdNode *Y) { DdNode* result = Cudd_CProjection(mgr, self,  Y); Cudd_Ref(result); return result; }
  int  MinHammingDist( IntArray *minterm, int upperBound) { return Cudd_MinHammingDist(mgr, self,  minterm->vec,  upperBound); }
%newobject Eval;   DdNode *  Eval( IntArray *inputs) { DdNode* result = Cudd_Eval(mgr, self,  inputs->vec); Cudd_Ref(result); return result; }
%newobject ShortestPath;   DdNode *  ShortestPath( IntArray *weight, IntArray *support, IntArray *length) { DdNode* result = Cudd_ShortestPath(mgr, self,  weight->vec,  support->vec,  length->vec); Cudd_Ref(result); return result; }
%newobject LargestCube;   DdNode *  LargestCube( IntArray *length) { DdNode* result = Cudd_LargestCube(mgr, self,  length->vec); Cudd_Ref(result); return result; }
  int  ShortestLength( IntArray *weight) { return Cudd_ShortestLength(mgr, self,  weight->vec); } 
%newobject Decreasing;   DdNode *  Decreasing( int i) { DdNode* result = Cudd_Decreasing(mgr, self,  i); Cudd_Ref(result); return result; }
%newobject Increasing;   DdNode *  Increasing( int i) { DdNode* result = Cudd_Increasing(mgr, self,  i); Cudd_Ref(result); return result; }
  int  EquivDC( DdNode *G, DdNode *D) { return Cudd_EquivDC(mgr, self,  G,  D); }
  int  EqualSupNorm( DdNode *g, CUDD_VALUE_TYPE tolerance, int pr) { return Cudd_EqualSupNorm(mgr, self,  g, tolerance,  pr); }
  DoubleArray*  CofMinterm() { double* tresult = Cudd_CofMinterm(mgr, self); int size = Cudd_ReadSize(mgr)+1; DoubleArray* result = new DoubleArray(size); result->Assign( tresult, size); return result; } 
%newobject SolveEqn;   /* DdNode *  SolveEqn( DdNode *Y, DdArray *G, int **yIndex, int n) { DdNode* result = Cudd_SolveEqn(mgr, self,  Y,  G->vec,  yIndex,  n); Cudd_Ref(result); return result; } */
%newobject VerifySol;   DdNode *  VerifySol( DdArray *G, IntArray *yIndex, int n) { DdNode* result = Cudd_VerifySol(mgr, self,  G->vec,  yIndex->vec,  n); Cudd_Ref(result); return result; }
%newobject SplitSet;   DdNode *  SplitSet( DdArray *xVars, int n, double m) { DdNode* result = Cudd_SplitSet(mgr, self,  xVars->vec,  n,  m); Cudd_Ref(result); return result; }
%newobject SubsetHeavyBranch;   DdNode *  SubsetHeavyBranch( int numVars, int threshold) { DdNode* result = Cudd_SubsetHeavyBranch(mgr, self,  numVars,  threshold); Cudd_Ref(result); return result; }
%newobject SupersetHeavyBranch;   DdNode *  SupersetHeavyBranch( int numVars, int threshold) { DdNode* result = Cudd_SupersetHeavyBranch(mgr, self,  numVars,  threshold); Cudd_Ref(result); return result; }
%newobject SubsetShortPaths;   DdNode *  SubsetShortPaths( int numVars, int threshold, int hardlimit) { DdNode* result = Cudd_SubsetShortPaths(mgr, self,  numVars,  threshold,  hardlimit); Cudd_Ref(result); return result; }
%newobject SupersetShortPaths;   DdNode *  SupersetShortPaths( int numVars, int threshold, int hardlimit) { DdNode* result = Cudd_SupersetShortPaths(mgr, self,  numVars,  threshold,  hardlimit); Cudd_Ref(result); return result; }
  int  BddToCubeArray( IntArray *y) { return Cudd_BddToCubeArray( mgr, self, y->vec); }
  int  PrintMinterm() { return Cudd_PrintMinterm(mgr, self); }
  int  PrintDebug( int n, int pr) { return Cudd_PrintDebug(mgr, self,  n,  pr); }
  int  EstimateCofactor( int i, int phase) { return Cudd_EstimateCofactor(mgr, self,  i,  phase); }
  double  CountMinterm( int nvars) { return Cudd_CountMinterm(mgr, self,  nvars); }
%newobject Support;   DdNode *  Support() { DdNode* result = Cudd_Support(mgr, self); Cudd_Ref(result); return result; }
  int  SupportSize() { return Cudd_SupportSize(mgr, self); }
  double  Density( int nvars) { return Cudd_Density(mgr, self,  nvars); }
  int NodeReadIndex () { return Cudd_NodeReadIndex(self); }
  int IsNonConstant() { return Cudd_IsNonConstant(self); }
  int DagSize() { return Cudd_DagSize(self); }
  int EstimateCofactorSimple(int i) { return Cudd_EstimateCofactorSimple(self, i); }
  double CountPath() { return Cudd_CountPath(self); }
  int CountLeaves() { return Cudd_CountLeaves(self); }
  int BddStore( char *ddname, char **varnames, IntArray *auxids, int mode, int varinfo, char *fname, FILE *fp) { return Dddmp_cuddBddStore( mgr, ddname, self, varnames, (int *) (auxids ? auxids->vec : NULL), mode, (Dddmp_VarInfoType) varinfo, fname, fp); }

  /* Risky - originally #Defines, not sure about referencing here */
  int IsConstant() { return Cudd_IsConstant(self); }
%newobject Not;   DdNode * Not() { DdNode* result = Cudd_Not(self); Cudd_Ref(result); return result;}
%newobject NotCond;   DdNode * NotCond(int c) { DdNode* result = Cudd_NotCond(self, c); Cudd_Ref(result); return result;}
%newobject Regular;   DdNode * Regular() { DdNode* result = Cudd_Regular(self); Cudd_Ref(result); return result;}
%newobject Complement;   DdNode * Complement() { DdNode* result = Cudd_Complement(self); Cudd_Ref(result); return result;}
  int IsComplement() { return Cudd_IsComplement(self); }
%newobject T;   DdNode * T() { DdNode* result = Cudd_T(self); Cudd_Ref(result); return result;}
%newobject E;   DdNode * E() { DdNode* result = Cudd_E(self); Cudd_Ref(result); return result;}
  double V() { return Cudd_V(self); }
  int ReadIndex(int index) { return Cudd_ReadPerm(mgr, index); }

  /* add specific */
%newobject addExistAbstract;   DdNode *  addExistAbstract( DdNode *cube) { DdNode* result = Cudd_addExistAbstract(mgr, self,  cube); Cudd_Ref(result); return result; }
%newobject addUnivAbstract;   DdNode *  addUnivAbstract( DdNode *cube) { DdNode* result = Cudd_addUnivAbstract(mgr, self,  cube); Cudd_Ref(result); return result; }
%newobject addOrAbstract;   DdNode *  addOrAbstract( DdNode *cube) { DdNode* result = Cudd_addOrAbstract(mgr, self,  cube); Cudd_Ref(result); return result; }
%newobject addFindMax;   DdNode *  addFindMax() { DdNode* result = Cudd_addFindMax(mgr, self); Cudd_Ref(result); return result; }
%newobject addFindMin;   DdNode *  addFindMin() { DdNode* result = Cudd_addFindMin(mgr, self); Cudd_Ref(result); return result; }
%newobject addIthBit;   DdNode *  addIthBit( int bit) { DdNode* result = Cudd_addIthBit(mgr, self,  bit); Cudd_Ref(result); return result; }
%newobject addScalarInverse;   DdNode *  addScalarInverse( DdNode *epsilon) { DdNode* result = Cudd_addScalarInverse(mgr, self,  epsilon); Cudd_Ref(result); return result; }
%newobject addIte;   DdNode *  addIte( DdNode *g, DdNode *h) { DdNode* result = Cudd_addIte(mgr, self,  g,  h); Cudd_Ref(result); return result; }
%newobject addIteConstant;   DdNode *  addIteConstant( DdNode *g, DdNode *h) { DdNode* result = Cudd_addIteConstant(mgr, self,  g,  h); Cudd_Ref(result); return result; }
%newobject addEvalConst;   DdNode *  addEvalConst( DdNode *g) { DdNode* result = Cudd_addEvalConst(mgr, self,  g); Cudd_Ref(result); return result; }
  int  addLeq(DdNode * g) { return Cudd_addLeq(mgr, self,   g); }
%newobject addCmpl;   DdNode *  addCmpl() { DdNode* result = Cudd_addCmpl(mgr, self); Cudd_Ref(result); return result; }
%newobject addNegate;   DdNode *  addNegate() { DdNode* result = Cudd_addNegate(mgr, self); Cudd_Ref(result); return result; }
%newobject addRoundOff;   DdNode *  addRoundOff( int N) { DdNode* result = Cudd_addRoundOff(mgr, self,  N); Cudd_Ref(result); return result; }
%newobject addCompose;   DdNode *  addCompose( DdNode *g, int v) { DdNode* result = Cudd_addCompose(mgr, self,  g,  v); Cudd_Ref(result); return result; }
%newobject addPermute;   DdNode *  addPermute( IntArray *permut) { DdNode* result = Cudd_addPermute(mgr, self,  permut->vec); Cudd_Ref(result); return result; }
%newobject addConstrain;   DdNode *  addConstrain( DdNode *c) { DdNode* result = Cudd_addConstrain(mgr, self,  c); Cudd_Ref(result); return result; }
%newobject addRestrict;   DdNode *  addRestrict( DdNode *c) { DdNode* result = Cudd_addRestrict(mgr, self,  c); Cudd_Ref(result); return result; }
%newobject addMatrixMultiply;   DdNode *  addMatrixMultiply( DdNode *B, DdArray *z, int nz) { DdNode* result = Cudd_addMatrixMultiply(mgr, self,  B,  z->vec,  nz); Cudd_Ref(result); return result; }
%newobject addTimesPlus;   DdNode *  addTimesPlus( DdNode *B, DdArray *z, int nz) { DdNode* result = Cudd_addTimesPlus(mgr, self,  B,  z->vec,  nz); Cudd_Ref(result); return result; }
%newobject addTriangle;   DdNode *  addTriangle( DdNode *g, DdArray *z, int nz) { DdNode* result = Cudd_addTriangle(mgr, self,  g,  z->vec,  nz); Cudd_Ref(result); return result; }
%newobject addVectorCompose;   DdNode *  addVectorCompose( DdArray *vector) { DdNode* result = Cudd_addVectorCompose(mgr, self,  vector->vec); Cudd_Ref(result); return result; }
%newobject addNonSimCompose;   DdNode *  addNonSimCompose( DdArray *vector) { DdNode* result = Cudd_addNonSimCompose(mgr, self,  vector->vec); Cudd_Ref(result); return result; }
%newobject addSwapVariables;   DdNode *  addSwapVariables( DdArray *x, DdArray *y, int n) { DdNode* result = Cudd_addSwapVariables(mgr, self,  x->vec,  y->vec,  n); Cudd_Ref(result); return result; }

  /* zbdd specific */
%newobject zddProduct;   DdNode *  zddProduct( DdNode *g) { DdNode* result = Cudd_zddProduct(mgr, self,  g); Cudd_Ref(result); return result; }
%newobject zddUnateProduct;   DdNode *  zddUnateProduct( DdNode *g) { DdNode* result = Cudd_zddUnateProduct(mgr, self,  g); Cudd_Ref(result); return result; }
%newobject zddWeakDiv;   DdNode *  zddWeakDiv( DdNode *g) { DdNode* result = Cudd_zddWeakDiv(mgr, self,  g); Cudd_Ref(result); return result; }
%newobject zddDivide;   DdNode *  zddDivide( DdNode *g) { DdNode* result = Cudd_zddDivide(mgr, self,  g); Cudd_Ref(result); return result; }
%newobject zddWeakDivF;   DdNode *  zddWeakDivF( DdNode *g) { DdNode* result = Cudd_zddWeakDivF(mgr, self,  g); Cudd_Ref(result); return result; }
%newobject zddDivideF;   DdNode *  zddDivideF( DdNode *g) { DdNode* result = Cudd_zddDivideF(mgr, self,  g); Cudd_Ref(result); return result; }
%newobject zddComplement;   DdNode *  zddComplement() { DdNode* result = Cudd_zddComplement(mgr, self); Cudd_Ref(result); return result; }
%newobject zddIte;   DdNode *  zddIte( DdNode *g, DdNode *h) { DdNode* result = Cudd_zddIte(mgr, self,  g,  h); Cudd_Ref(result); return result; }
%newobject zddUnion;   DdNode *  zddUnion( DdNode *Q) { DdNode* result = Cudd_zddUnion(mgr, self,  Q); Cudd_Ref(result); return result; }
%newobject zddIntersect;   DdNode *  zddIntersect( DdNode *Q) { DdNode* result = Cudd_zddIntersect(mgr, self,  Q); Cudd_Ref(result); return result; }
%newobject zddDiff;   DdNode *  zddDiff( DdNode *Q) { DdNode* result = Cudd_zddDiff(mgr, self,  Q); Cudd_Ref(result); return result; }
%newobject zddDiffConst;   DdNode *  zddDiffConst( DdNode *Q) { DdNode* result = Cudd_zddDiffConst(mgr, self,  Q); Cudd_Ref(result); return result; }
%newobject zddSubset1;   DdNode *  zddSubset1( int var) { DdNode* result = Cudd_zddSubset1(mgr, self,  var); Cudd_Ref(result); return result; }
%newobject zddSubset0;   DdNode *  zddSubset0( int var) { DdNode* result = Cudd_zddSubset0(mgr, self,  var); Cudd_Ref(result); return result; }
%newobject zddChange;   DdNode *  zddChange( int var) { DdNode* result = Cudd_zddChange(mgr, self,  var); Cudd_Ref(result); return result; }
  int  zddCount() { return Cudd_zddCount(mgr, self); }
  double  zddCountDouble() { return Cudd_zddCountDouble(mgr, self); }
  int  zddPrintMinterm() { return Cudd_zddPrintMinterm(mgr, self); }
  int  zddPrintCover() { return Cudd_zddPrintCover(mgr, self); }
  int  zddPrintDebug( int n, int pr) { return Cudd_zddPrintDebug(mgr, self,  n,  pr); }
  double  zddCountMinterm( int path) { return Cudd_zddCountMinterm(mgr, self,  path); }
%newobject zddIsop;   DdNode *  zddIsop( DdNode *U, DdArray *zdd_I) { DdNode* result = Cudd_zddIsop(mgr, self,  U,  zdd_I->vec); Cudd_Ref(result); return result; }
  int zddDagSize(DdNode *p_node) { return Cudd_zddDagSize(self); }

  /* apa specific */
  int ApaPrintMinterm(FILE *fp, int nvars) { return Cudd_ApaPrintMinterm(fp, mgr, self, nvars); }
  int ApaPrintMintermExp(FILE *fp, int nvars, int precision) { return Cudd_ApaPrintMintermExp(fp, mgr, self, nvars, precision); }
  int ApaPrintDensity(FILE *fp, int nvars) { return Cudd_ApaPrintDensity(fp, mgr, self, nvars); }
  DdApaNumber ApaCountMinterm(int nvars, IntArray *digits) {  return Cudd_ApaCountMinterm(mgr, self, nvars, digits->vec); }

  /* Added to DdNode */
  int __hash__ () {
    return (long int)(self);
  }

  int __int__ () {
    return (long int)(self);
  }

%newobject __and__;  DdNode* __and__ (DdNode* other) {
    DdNode *result = Cudd_bddAnd(mgr, self, other);
    Cudd_Ref(result);
    return result;
  }
  
%newobject __or__;  DdNode* __or__ (DdNode* other) {
    DdNode *result = Cudd_bddOr(mgr, self, other);
    Cudd_Ref(result);
    return result;
  }
  
%newobject __xor__;  DdNode* __xor__ (DdNode* other) {
    DdNode *result = Cudd_bddXor(mgr, self, other);
    Cudd_Ref(result);
    return result;
  }
  
%newobject __invert__;  DdNode* __invert__ () {
    DdNode *result = Cudd_Not(self);
    Cudd_Ref(result);
    return result;
  }
 
%newobject __rshift__;  DdNode* __rshift__ (DdNode* other) {
    DdNode *result = Cudd_Not(Cudd_bddAnd(mgr, self, Cudd_Not(other))); 
    Cudd_Ref(result);
    return result;
  }

  bool __cmp__ (DdNode* other) {
    if (self == other) return FALSE;
    return TRUE;
  }

%newobject __sub__;  DdNode* __sub__ (DdNode* other) {
    DdNode *result = Cudd_bddAnd(mgr,self,Cudd_Not(other));
    Cudd_Ref(result);
    return result;
  }
  
%newobject __add__;  DdNode* __add__ (DdNode* other) {
    DdNode *result = Cudd_bddOr(mgr, self, other);
    Cudd_Ref(result);
    return result;
  }

  bool __lt__(DdNode* other) {
    return Cudd_bddLeq(mgr, self,  other) && self != other ? TRUE : FALSE;
  }
  
  bool __le__(DdNode* other) {
    return Cudd_bddLeq(mgr, self,  other) ? TRUE : FALSE;
  }
  
  bool __eq__(DdNode* other) {
    return self == other ? TRUE : FALSE;
  }
  
  bool __ne__(DdNode* other) {
    return self != other ? TRUE : FALSE;
  }
  
  // Note that a > b  is defined as b <= a and b != a. 
  bool __gt__(DdNode* other) {
    return Cudd_bddLeq(mgr, other,  self) && self != other ? TRUE : FALSE;
  }

  // Note that a >= b  is defined as b <= a. 
  bool __ge__(DdNode* other) {
    return Cudd_bddLeq(mgr, other,  self) ? TRUE : FALSE;
  }
  
  // Define non-zero as not equal to logic zero
  bool __nonzero__() {
    return self == Cudd_ReadLogicZero(mgr) ? FALSE : TRUE; 
  }

  int __len__() {
    return Cudd_DagSize(self);
  }

  int SizeOf() {
    return sizeof(*self);
  }

  void Show(char* name, int op1, int op2) {
    printf("BDD Name: %s\n",name);
    Cudd_PrintDebug(mgr,self,op1,op2);
  }

  bool Empty() {
    if (self == Cudd_ReadLogicZero(mgr))
       return TRUE;
    return FALSE;
  }

  int DumpDot() {

    FILE *dfp = NULL;
    DdNode *dfunc[1];
    int retval;    
    
    dfunc[0] = self;
    dfp = fopen("out.dot", "w");
    
    retval = Cudd_DumpDot(mgr,1,dfunc,NULL,NULL,dfp);
 
    fclose(dfp);
    return retval;
  }

  int DumpBlif() {

    FILE *dfp = NULL;
    DdNode *dfunc[1];
    int retval;    
    
    dfunc[0] = self;
    dfp = fopen("out.blif", "w");
    
    retval = Cudd_DumpBlif(mgr,1,dfunc,NULL,NULL,NULL,dfp,0);
 
    fclose(dfp);
    return retval;
  }

  DdArray* Vector() {
  
    DdArray* result;
    DdNode *front, *f1, *f0;
    int index;
    int size = Cudd_DagSize(self);
    size = size-1;
  
    if (size > Cudd_ReadSize(mgr)) {
      cerr << "Minterm contains more nodes than manager!\n";
      return NULL;
    }

    result = new DdArray(size);
    if (!size) return result;

    front = self;
 
    index = Cudd_NodeReadIndex(front);
    
    result->__setitem__(0,Cudd_bddIthVar(mgr,index));

    for (int i=1; i< size; i++) {      
      f1 = Cudd_T(front);
      f0 = Cudd_E(front);
     
      if ( (f1 != Cudd_ReadLogicZero(mgr)) && (f1 != Cudd_ReadOne(mgr)) ) {
        if (!( (f0 == Cudd_ReadLogicZero(mgr)) || (f0 == Cudd_ReadOne(mgr)) )) {
          cerr << "Not a minterm\n";
          delete result;
          return NULL;
        }
        front = f1;
      } else if ( (f0 != Cudd_ReadLogicZero(mgr)) && (f0 != Cudd_ReadOne(mgr)) ) {
        if (!( (f1 == Cudd_ReadLogicZero(mgr)) || (f1 == Cudd_ReadOne(mgr)) )) {
          cerr << "Not a minterm\n";
          delete result;
          return NULL;
        }
        front = f0;
      } else {
        cerr << "Not enough nodes in minterm\n";
        delete result;
        return NULL;
      }
      index = Cudd_NodeReadIndex(front);
      result->__setitem__(i,Cudd_bddIthVar(mgr,index));
    }

    return result;
 
  }

};

#if CUDDVER >= 0x020400
// NodePair is a helper struct used for prime enumeration
%{
struct NodePair {
  DdNode * lower;
  DdNode * upper;
};
%}

struct NodePair { };

%extend NodePair {
%pythoncode %{
def __iter__(self):
  global iter_meth
  if iter_meth != 2:
    print "Can only enumerate primes for a NodePair. Setting iter_meth == 2 and proceeding"
    iter_meth == 2
  return ForeachPrimeIterator(self)
__doc__="This is used to provide the functionality of prime enumeration in CUDD 2.4.0. Create the NodePair by passing the DdNodes for lower and upper to the constructor. Once that is done, you can iterate over the primes of the NodePair using the Python for statement. There is no need to do this if you are interested in the primes of a simple DdNode -- the package automatically creates the NodePair and destroys it in that case."

%}

  NodePair(DdNode *lwr, DdNode *upr) {
    NodePair *res;
    res = (NodePair *) malloc(sizeof(NodePair));
    res->lower = lwr;
    res->upper = upr;
    return res;
  }

  ~NodePair() {
    free(self);
  }

  // Not expected to be used directly -- use a for loop	  
%newobject LOWER;  DdNode *LOWER() { return self->lower; }
%newobject UPPER;  DdNode *UPPER() { return self->upper; }

  int FirstPrime(DdGen *gen, int **dum_cube) {
    if (Cudd_IsGenEmpty(gen)) { /* Happens if you call the generator on Logic Zero */ return 0; }
    return 1;
  }
  
  int NextPrime(DdGen *gen, int **dum_cube) {
    int tmp;
    if (!gen) { /* Something is seriously wrong ! */ assert(0); }
    if (Cudd_IsGenEmpty(gen)) { // We should never hit this -- raise StopIteration in python earlier.
      fprintf(Cudd_ReadStdout(mgr),"You shouldn\'t be here! Fix your Python iterator.");
      return 0;
    }
    else { // Have a cube to return
      tmp = Cudd_NextPrime(gen, dum_cube);
      if (tmp <= 0) { // The freakin' generator is already empty ...
	assert(Cudd_IsGenEmpty(gen));
	return 0;
      }
      return 1;
    }
  }

};
#endif
