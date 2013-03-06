/* $Id: cuddauxCompose.c,v 1.2 2005/06/14 14:37:56 bjeannet Exp $ */
/**CFile***********************************************************************

  FileName    [cuddauxCompose.c]

  PackageName [cuddaux]

  Synopsis    [Functional composition and variable permutation of DDs.]

  Description [External procedures included in this module:
		<ul>
		<li> Cuddaux_addCompose()
		<li> Cuddaux_AddVarMap()
		<li> Cuddaux_SetVarMap()
		<li> Cuddaux_addVectorCompose()
		<li> Cuddaux_addApplyVectorCompose()
		</ul>
	       Internal procedures included in this module:
		<ul>
		<li> cuddauxAddComposeRecur()
		</ul>
	       Static procedures included in this module:
		<ul>
		<li> cuddauxAddVarMapRecur()
		<li> cuddauxAddVectorComposeRecur()
		<li> CuddauxAddApplyVectorCompose()
	       </ul>
  The permutation functions use a local cache because the results to
  be remembered depend on the permutation being applied.  Since the
  permutation is just an array, it cannot be stored in the global
  cache. There are different procedured for BDDs and ADDs. This is
  because bddPermuteRecur uses cuddBddIteRecur. If this were changed,
  the procedures could be merged.]

  Author      [Bertrand Jeannet]

  Copyright   []

******************************************************************************/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include "cuddInt.h"
#include "util.h"
#include "st.h"

#include "cuddaux.h"

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Substitutes g for x_v in the ADD for f.]

  Description [Substitutes g for x_v in the ADD for f. v is the index of the
  variable to be substituted. g must be a BDD. Cuddaux_addCompose passes
  the corresponding projection function to the recursive procedure, so
  that the cache may be used.  Returns the composed ADD if successful;
  NULL otherwise.]

  SideEffects [None]

  SeeAlso     [Cudd_bddCompose]

******************************************************************************/
DdNode *
Cuddaux_addCompose(
  DdManager * dd,
  DdNode * f,
  DdNode * g,
  int  v)
{
    DdNode *proj, *res;

    /* Sanity check. */
    if (v < 0 || v > dd->size) return(NULL);

    proj = dd->vars[v];
    do {
	dd->reordered = 0;
	res = cuddauxAddComposeRecur(dd,f,g,proj);
    } while (dd->reordered == 1);
    return(res);

} /* end of Cuddaux_addCompose */

/**Function********************************************************************

  Synopsis [Registers a variable mapping (permutation) with the manager.]

  Description [Registers with the manager a variable mapping (permutation) described
  by the array permut. There should be an entry in array permut
  for each variable in the manager. The i-th entry of permut holds the
  index of the variable that is to substitute the i-th variable.
  This variable mapping is then used by
  functions like Cudd_bddVarMap.  This function is convenient for
  those applications that perform the same mapping several times.
  However, if several different permutations are used, it may be more
  efficient not to rely on the registered mapping, because changing
  mapping causes the cache to be cleared.  (The initial setting,
  however, does not clear the cache.) When new variables are created, the
  map is automatically extended (each new variable maps to
  itself). The typical use, however, is to wait until all variables
  are created, and then create the map.  Returns 1 if the mapping is
  successfully registered with the manager; 0 otherwise.]

  SideEffects [Modifies the manager. May clear the cache.]

  SeeAlso     [Cudd_bddVarMap Cuddaux_addVarMap Cudd_SetVarMap]

******************************************************************************/
int
Cuddaux_SetVarMap(DdManager *dd, int* array, int size)
{
  int i;

  if (dd->map != NULL) {
    cuddCacheFlush(dd);
  } else {
    dd->map = ALLOC(int,dd->maxSize);
    if (dd->map == NULL) {
      dd->errorCode = CUDD_MEMORY_OUT;
      return(0);
    }
    dd->memused += sizeof(int) * dd->maxSize;
  }
  if (size>dd->maxSize) size=dd->maxSize;
  for (i = 0; i < size; i++) {
    dd->map[i] = array[i];
  }
  for (i = size; i<dd->maxSize; i++){
    dd->map[i] = i;
  }
  return(1);
} /* end of Cuddaux_SetVarMap */


/**Function********************************************************************

  Synopsis    [Remaps the variables of an ADD using the default variable map.]

  Description [Remaps the variables of an ADD using the default
  variable map.  A typical use of this function is to swap two sets of
  variables.  The variable map must be registered with Cudd(aux)_SetVarMap.
  Returns a pointer to the resulting ADD if successful; NULL
  otherwise.]

  SideEffects [None]

  SeeAlso     [Cudd_SetVarMap Cuddaux_SetVarMap]

******************************************************************************/
DdNode *
Cuddaux_addVarMap(
  DdManager * manager /* DD manager */,
  DdNode * f /* function in which to remap variables */)
{
    DdNode *res;

    if (manager->map == NULL) return(NULL);
    do {
	manager->reordered = 0;
	res = cuddauxAddVarMapRecur(manager, f);
    } while (manager->reordered == 1);

    return(res);

} /* end of Cuddaux_addVarMap */


/**Function********************************************************************

  Synopsis    [Composes an BDD with a vector of BDDs.]

  Description [Given a vector of BDDs, creates a new BDD by
  substituting the BDDs for the variables of the BDD f.  There
  should be an entry in vector for each variable in the manager.
  If no substitution is sought for a given variable, the corresponding
  projection function should be specified in the vector.
  This function implements simultaneous composition.
  Returns a pointer to the resulting BDD if successful; NULL
  otherwise.]

  SideEffects [None]

  SeeAlso     [Cudd_addVectorCompose Cudd_addNonSimCompose Cudd_addPermute
  Cudd_addCompose Cudd_bddVectorCompose]

******************************************************************************/
DdNode*
Cuddaux_bddVectorComposeCommon(struct common* common,
			       DdNode * f,
			       DdNode ** vector)
{
  DdNode *res;
  DdManager* dd = common->man->man;
  int i, deepest;

  do {
    dd->reordered = 0;
    if (cuddauxCommonReinit(common)==NULL) return NULL;
    /* Find deepest real substitution. */
    for (deepest = dd->size - 1; deepest >= 0; deepest--) {
      i = dd->invperm[deepest];
      if (vector[i] != dd->vars[i]) {
	break;
      }
    }
    /* Recursively solve the problem. */
    res = cuddauxBddVectorComposeRecur(common,f,vector,deepest);
  } while (dd->reordered == 1);
  return(res);
} /* end of Cuddaux_bddVectorComposeCommon */

DdNode*
Cuddaux_bddPermuteCommon(struct common* common,
			 DdNode* f,
			 int* permut)
{
  DdManager* dd = common->man->man;
  const int size = dd->size;
  DdNode** vector;
  DdNode* res;
  int i;

  vector = malloc(dd->size*sizeof(DdNode*));
  for (i=0; i<size;i++){
    int j = permut[i];
    if (j<0 || j>=size){
      fprintf(stderr,"mlcuddidl: error, permutation contains a not yet existing BDD index %d\n",j);
      free(vector);
      dd->errorCode = CUDD_INVALID_ARG;
      return NULL;
    }
    vector[i] = dd->vars[j];
  }
  res = Cuddaux_bddVectorComposeCommon(common,f,vector);
  free(vector);
  return res;
}

/**Function********************************************************************

  Synopsis    [Composes an ADD with a vector of BDDs.]

  Description [Given a vector of BDDs, creates a new ADD by
  substituting the BDDs for the variables of the ADD f.  There
  should be an entry in vector for each variable in the manager.
  If no substitution is sought for a given variable, the corresponding
  projection function should be specified in the vector.
  This function implements simultaneous composition.
  Returns a pointer to the resulting ADD if successful; NULL
  otherwise.]

  SideEffects [None]

  SeeAlso     [Cudd_addVectorCompose Cudd_addNonSimCompose Cudd_addPermute
  Cudd_addCompose Cudd_bddVectorCompose]

******************************************************************************/
DdNode *
Cuddaux_addVectorComposeCommon(struct common* common,
			       DdNode * f,
			       DdNode ** vector)
{
  DdNode *res;
  DdManager* dd = common->man->man;
  int i, deepest;

  do {
    dd->reordered = 0;
    if (cuddauxCommonReinit(common)==NULL) return NULL;
    /* Find deepest real substitution. */
    for (deepest = dd->size - 1; deepest >= 0; deepest--) {
      i = dd->invperm[deepest];
      if (vector[i] != dd->vars[i]) {
	break;
      }
    }
    /* Recursively solve the problem. */
    res = cuddauxAddVectorComposeRecur(common,f,vector,deepest);
  } while (dd->reordered == 1);
  return(res);
} /* end of Cudd_addVectorCompose */

DdNode*
Cuddaux_addPermuteCommon(struct common* common,
			 DdNode* f,
			 int* permut)
{
  DdManager* dd = common->man->man;
  const int size = dd->size;
  DdNode** vector;
  DdNode* res;
  int i;

  vector = malloc(dd->size*sizeof(DdNode*));
  for (i=0; i<size;i++){
    int j = permut[i];
    if (j<0 || j>=size){
      fprintf(stderr,"mlcuddidl: error, permutation contains a not yet existing BDD index %d\n",j);
      free(vector);
      dd->errorCode = CUDD_INVALID_ARG;
      return NULL;
    }
    vector[i] = dd->vars[j];
  }
  res = Cuddaux_addVectorComposeCommon(common,f,vector);
  free(vector);
  return res;
}

DdNode *
Cuddaux_addVectorCompose(
    struct CuddauxMan* man,
    DdNode * f,
    DdNode ** vector
)
{
  struct common common;
  struct CuddauxHash hash;
  DdNode* res;
  common.pid = 0;
  common.arity = 1;
  common.memo.discr = Hash;
  common.memo.u.hash = &hash;
  common.man = man;
  hash.hash = NULL;
  hash.arity = 1;
  hash.initialsize = 0;
  hash.man = NULL;
  res = Cuddaux_addVectorComposeCommon(&common,f,vector);
  if (res!=NULL) cuddRef(res);
  cuddauxCommonClear(&common);
  if (res!=NULL) cuddDeref(res);
  return res;
}

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cudd_addCompose.]

  Description [Performs the recursive step of Cudd_addCompose.
  Returns the composed ADD if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     [Cudd_addCompose]

******************************************************************************/
DdNode *
cuddauxAddComposeRecur(
  DdManager * dd,
  DdNode * f,
  DdNode * g,
  DdNode * proj)
{
  DdNode *G, *f1, *f0, *g1, *g0, *r, *t, *e;
  unsigned int v, topf, topg, top;
  int index=-1;

  v = dd->perm[proj->index];
  topf = cuddI(dd,f->index);

  /* Terminal case. Subsumes the test for constant f. */
  if (topf > v)
    return(f);
  if (topf == v) {
    /* Compose. */
    f1 = cuddT(f);
    f0 = cuddE(f);
    r = cuddauxAddIteRecur(dd, g, f1, f0);
    if (r == NULL) return(NULL);
    return(r);
  }
  /* Check cache. */
  r = cuddCacheLookup(dd,DDAUX_ADD_COMPOSE_RECUR_TAG,f,g,proj);
  if (r != NULL) {
    return(r);
  }
  /* Compute cofactors of f and g. Remember the index of the top
  ** variable.
  */
  G = Cudd_Regular(g);
  topg = cuddI(dd,G->index);
  top = ddMin(topf,topg);
  if (topf == top) {
    index = f->index;
    f1 = cuddT(f);
    f0 = cuddE(f);
  }
  else {
    f1 = f0 = f;
  }
  if (topg == top){
    index = G->index;
    g1 = cuddT(G);
    g0 = cuddE(G);
    if (Cudd_IsComplement(g)){
      g1 = Cudd_Not(g1);
      g0 = Cudd_Not(g0);
    }
  }
  else {
    g1 = g0 = g;
  }
  /* Recursive step. */
  t = cuddauxAddComposeRecur(dd, f1, g1, proj);
  if (t == NULL) return(NULL);
  cuddRef(t);
  e = cuddauxAddComposeRecur(dd, f0, g0, proj);
  if (e == NULL) {
    Cudd_RecursiveDeref(dd, t);
    return(NULL);
  }
  cuddRef(e);

  r = (t==e) ? t : cuddUniqueInter(dd, (int) index, t, e);
  if (r == NULL) {
    Cudd_RecursiveDeref(dd, t);
    Cudd_RecursiveDeref(dd, e);
    return(NULL);
  }
  cuddDeref(t);
  cuddDeref(e);

  cuddCacheInsert(dd,DDAUX_ADD_COMPOSE_RECUR_TAG,f,g,proj,r);

  return(r);

} /* end of cuddauxAddComposeRecur */

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Implements the recursive step of Cuddaux_addVarMap.]

  Description [Implements the recursive step of Cuddaux_addVarMap.
  Returns a pointer to the result if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     [Cudd_addVarMap]

******************************************************************************/
DdNode *
cuddauxAddVarMapRecur(DdManager *manager, DdNode* f)
{
  DdNode        *T, *E;
  DdNode        *res;
  int           index;

  /* Check for terminal case of constant node. */
  if (cuddIsConstant(f)) {
    return(f);
  }

  /* If problem already solved, look up answer and return. */
  if (f->ref != 1 &&
      (res = cuddCacheLookup1(manager,Cuddaux_addVarMap,f)) != NULL) {
	return res;
      }

  /* Split and recur on children of this node. */
  T = cuddauxAddVarMapRecur(manager,cuddT(f));
  if (T == NULL) return(NULL);
  cuddRef(T);
  E = cuddauxAddVarMapRecur(manager,cuddE(f));
  if (E == NULL) {
    Cudd_RecursiveDeref(manager, T);
    return(NULL);
  }
  cuddRef(E);

  /* Move variable that should be in this position to this position
  ** by retrieving the single var BDD for that variable, and calling
  ** cuddBddIteRecur with the T and E we just created.
  */
  index = manager->map[f->index];
  res = cuddauxAddIteRecur(manager,manager->vars[index],T,E);
  if (res == NULL) {
    Cudd_RecursiveDeref(manager, T);
    Cudd_RecursiveDeref(manager, E);
    return(NULL);
  }
  cuddRef(res);
  Cudd_RecursiveDeref(manager, T);
  Cudd_RecursiveDeref(manager, E);
  cuddDeref(res);

  /* Do not keep the result if the reference count is only 1, since
  ** it will not be visited again.
  */
  if (f->ref != 1) {
    cuddCacheInsert1(manager,Cuddaux_addVarMap,f,res);
  }
  return(res);
}

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cuddaux_addVectorCompose.]

  Description []

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode*
cuddauxAddVectorComposeRecur(
			     struct common* common,
			     DdNode * f /* ADD in which to compose */,
			     DdNode ** vector /* functions to substitute */,
			     int  deepest /* depth of deepest substitution */)
{
  DdManager* dd = common->man->man;
  DdNode *T,*E;
  DdNode *res;

  /* If we are past the deepest substitution, return f. */
  if (cuddI(dd,f->index) > deepest) {
    return(f);
  }

  /* Check cache. */
  res = cuddauxCommonLookup1(common,f);
  if (res != NULL) return res;

  /* Split and recur on children of this node. */
  T = cuddauxAddVectorComposeRecur(common,cuddT(f),vector,deepest);
  if (T == NULL)  return(NULL);
  cuddRef(T);
  E = cuddauxAddVectorComposeRecur(common,cuddE(f),vector,deepest);
  if (E == NULL) {
    Cudd_RecursiveDeref(dd, T);
    return(NULL);
  }
  cuddRef(E);

  /* Retrieve the 0-1 ADD for the current top variable and call
  ** cuddauxAddIteRecur with the T and E we just created.
  */
  res = cuddauxAddIteRecur(dd,vector[f->index],T,E);
  if (res == NULL) {
    Cudd_RecursiveDeref(dd, T);
    Cudd_RecursiveDeref(dd, E);
    return(NULL);
  }
  cuddRef(res);
  Cudd_RecursiveDeref(dd, T);
  Cudd_RecursiveDeref(dd, E);
  cuddDeref(res);

  return cuddauxCommonInsert1(common,f,res);
} /* end of cuddauxAddVectorComposeRecur */

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cuddaux_bddVectorCompose.]

  Description []

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode *
cuddauxBddVectorComposeRecur(
			     struct common* common,
			     DdNode * f /* BDD in which to compose */,
			     DdNode ** vector /* functions to be composed */,
			     int deepest /* depth of the deepest substitution */)
{
  DdManager* dd = common->man->man;
  DdNode	*F,*T,*E;
  DdNode	*res;

  statLine(dd);
  F = Cudd_Regular(f);

  /* If we are past the deepest substitution, return f. */
  if (cuddI(dd,F->index) > deepest) {
    return(f);
  }

  /* If problem already solved, look up answer and return. */
  res = cuddauxCommonLookup1(common,F);
  if (res != NULL){
    return(Cudd_NotCond(res,F != f));
  }

  /* Split and recur on children of this node. */
  T = cuddauxBddVectorComposeRecur(common,cuddT(F),vector, deepest);
  if (T == NULL) return(NULL);
  cuddRef(T);
  E = cuddauxBddVectorComposeRecur(common,cuddE(F),vector, deepest);
  if (E == NULL) {
    Cudd_IterDerefBdd(dd, T);
    return(NULL);
  }
  cuddRef(E);

  /* Call cuddBddIteRecur with the BDD that replaces the current top
  ** variable and the T and E we just created.
  */
  res = cuddBddIteRecur(dd,vector[F->index],T,E);
  if (res == NULL) {
    Cudd_IterDerefBdd(dd, T);
    Cudd_IterDerefBdd(dd, E);
    return(NULL);
  }
  cuddRef(res);
  Cudd_IterDerefBdd(dd, T);
  Cudd_IterDerefBdd(dd, E);
  cuddDeref(res);

  res = cuddauxCommonInsert1(common,f,res);
  res = Cudd_NotCond(res,F != f);
  return res;
} /* end of cuddauxBddVectorComposeRecur */
