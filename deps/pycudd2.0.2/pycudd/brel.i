%{
#ifndef FROM_PYCUDDI
#error Use only from pycudd.i. Make sure to define FROM_PYCUDDI
#endif
%}

typedef struct BrelContext { } BrelContext_t;

%extend BrelContext_t {
  BrelContext_t() {
    BrelContext_t *context;
    BrelParams_t *params;

    context=ALLOC(BrelContext_t,1);
    params=ALLOC(BrelParams_t,1);
    BrelDefaultParams(params);

    context->args=NULL;
    context->Minimize=(Brel_Minimize)Brel_ISOP;
    context->Cost=(Brel_CalculateCost)Brel_SharedBddSize; 
    context->FreeCost=(Brel_FreeCost)Brel_FreeDouble; 
    context->CmpCost=(Brel_CmpCost)Brel_CmpDouble;

    context->HCost=(Brel_CalculateCost)Brel_SharedBddSize;
  
    context->HFreeCost=(Brel_FreeCost)Brel_FreeDouble; 
    context->HCmpCost=(Brel_CmpCost)Brel_CmpDouble;   
    context->params=params;
 
    return context;
  }
}

typedef struct BrelRelation { } BrelRelation_t;

%extend BrelRelation_t {
  BrelRelation_t(DdNode *relation, DdArray *inps, DdArray *ops) {
    
    BrelRelation_t *sbrrel;
    int i;
    DdNode **tmp;

    sbrrel=ALLOC(BrelRelation_t,1);
    sbrrel->numin    = inps->sz;
    sbrrel->numout   = ops->sz;
    sbrrel->bestcost = BRELMAXSOL;
    sbrrel->numsol   = 0;
    sbrrel->bddsol   = NULL;
    // We want the I/O vars to be a copy of the DdArray arguments -- not a pointer to a mutable array!
    sbrrel->inrel    = ALLOC(DdNode *,sbrrel->numin);
    sbrrel->outrel   = ALLOC(DdNode *,sbrrel->numout);
    // Need to increase the ref counts of the I/O DdNodes ... 
    for (i=0; i < inps->sz; i++) { sbrrel->inrel[i] = inps->vec[i]; Cudd_Ref(inps->vec[i]); }
    for (i=0; i < ops->sz; i++) { sbrrel->outrel[i] = ops->vec[i]; Cudd_Ref(ops->vec[i]); }
    sbrrel->relation = relation;
    // And of the relation -- we want the extra reference
    Cudd_Ref(relation);
    sbrrel->ddman=mgr;
    return sbrrel;
  }

  ~BrelRelation_t() {
    if (self->inrel != NULL and mgr) { for (DdNode **tmp=self->inrel; tmp < self->inrel+self->numin; tmp++) Cudd_RecursiveDeref(mgr, *tmp); } 
    BRELFREE(self->inrel);
    if (self->outrel != NULL and mgr) { for (DdNode **tmp=self->outrel; tmp < self->outrel+self->numout; tmp++) Cudd_RecursiveDeref(mgr, *tmp); }
    BRELFREE(self->outrel);
    if (mgr) Cudd_RecursiveDeref(mgr, self->relation);
    if (self->bddsol != NULL and mgr) { for (DdNode **tmp=self->bddsol; tmp < self->bddsol+self->numout; tmp++) Cudd_RecursiveDeref(mgr, *tmp); }
    BRELFREE(self->bddsol);
    if (mgr) Cudd_RecursiveDeref(mgr,self->relation);
  }

  DdArray* SolveRelation(BrelContext_t *ctxt = NULL) {
    DdNode **soln;
    DdArray *result;
    DdNode *opcube;
    DdNode *tmp;
    int i;
    // Create a cube of the output variables from the DdNode ** that we have
    opcube = self->outrel[0];
    Cudd_Ref(opcube);
    for (i=1; i<self->numout; i++) {
      tmp = Cudd_bddAnd(mgr,self->outrel[i],opcube);
      Cudd_Ref(tmp);
      Cudd_RecursiveDeref(mgr,opcube);
      opcube = tmp;
    }
    self->bddsol = Brel_Solve(mgr,self->relation,opcube,(Brel_Context_t *) ctxt);
    // Done with opcube
    Cudd_RecursiveDeref(mgr, opcube);
    result = new DdArray(self->numout);
    result->Assign(self->bddsol,self->numout);
    return result;
  }
}
