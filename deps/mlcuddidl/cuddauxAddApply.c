/**CFile***********************************************************************

  FileName    [cuddauxAddApply.c]

  PackageName [cuddaux]

  Synopsis    [Variation of cuddAddApply.c module,
	       using a local cache (easier for interfacing
	       with external languages like OCaml]

  Description [Miscellaneous operations..]

	    External procedures included in this module:
		<ul>
		<li> Cuddaux_addApply1()
		<li> Cuddaux_addApply2()
		<li> Cuddaux_addTest2()
		<li> Cuddaux_addApply3()
		<li> Cuddaux_addAbstract()
		<li> Cuddaux_addBddAndAbstract()
		<li> Cuddaux_addApplyBddAndAbstract()
		</ul>
	    Internal procedures included in this module:
		<ul>
		<li> cuddauxAddApply1Recur()
		<li> cuddauxAddApply2Recur()
		<li> cuddauxAddApply3Recur()
		<li> cuddauxAddTest2Recur()
		<li> cuddauxAddAbstractRecur()
		<li> cuddauxAddBddAndAbstractRecur()
		<li> cuddauxAddApplyBddAndAbstractRecur()
		</ul>
		]

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

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
static int bddCheckPositiveCube (DdManager *manager, DdNode *cube);

/**AutomaticEnd***************************************************************/

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Applies op to the discriminants of f.]

  Description [Applies op to the discriminants of f.
  Returns a pointer to the result if succssful; NULL otherwise.

  Be careful to put a hook to reinitialize the table in case of reordering
  ]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode *
Cuddaux_addApply1(struct op1* op,
		  DdNode * f)
{
  DdNode *res;
  DdManager* dd = op->common1.man->man;
  do {
    dd->reordered = 0;
    if (cuddauxCommonReinit(&op->common1)==NULL) return NULL;
    res = cuddauxAddApply1Recur(dd,op,f);
  } while (dd->reordered == 1);
  return(res);

} /* end of Cuddaux_addApply1 */

/**Function********************************************************************

  Synopsis    [Applies op to the corresponding discriminants of f and g.]

  Description [Applies op to the corresponding discriminants of f and g.
  Returns a pointer to the result if succssful; NULL otherwise.

  Be careful to put a hook to reinitialize the table in case of reordering
  ]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode *
Cuddaux_addApply2(struct op2* op,
		  DdNode * f,
		  DdNode * g)
{
  DdNode *res;
  DdManager* dd = op->common2.man->man;

  do {
    dd->reordered = 0;
    if (cuddauxCommonReinit(&op->common2)==NULL) return NULL;
    res = cuddauxAddApply2Recur(dd,op,f,g);
  } while (dd->reordered == 1);
  return(res);
} /* end of Cuddaux_addApply2 */

/**Function********************************************************************

  Synopsis    [Applies op to the corresponding discriminants of f and g.]

  Description [Applies op to the corresponding discriminants of f and g.
  Returns a pointer to the result if succssful; NULL otherwise.

  Be careful to put a hook to reinitialize the table in case of reordering
  ]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
int
Cuddaux_addTest2(struct test2* op,
		 DdNode * f,
		 DdNode * g)
{
  DdNode *res;
  int ret;
  DdManager* dd = op->common2t.man->man;

  do {
    dd->reordered = 0;
    if (cuddauxCommonReinit(&op->common2t)==NULL) return -1;
    res = cuddauxAddTest2Recur(dd,op,f,g);
  } while (dd->reordered == 1);
  ret = res==NULL ? (-1) : (res==DD_ONE(dd));
  return ret;
} /* end of Cuddaux_addTest2 */

/**Function********************************************************************

  Synopsis    [Applies op to the corresponding discriminants of f, g and h.]

  Description [Applies op to the corresponding discriminants of f, g and h.
  Returns a pointer to the result if succssful; NULL otherwise.

  Be careful to put a hook to reinitialize the table in case of reordering
  ]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/

DdNode*
Cuddaux_addApply3(struct op3* op,
		  DdNode * f,
		  DdNode * g,
		  DdNode * h)
{
  DdNode *res;
  DdManager* dd = op->common3.man->man;
  do {
    dd->reordered = 0;
    if (cuddauxCommonReinit(&op->common3)==NULL) return NULL;
    res = cuddauxAddApply3Recur(dd,op,f,g,h);
  } while (dd->reordered == 1);
  return(res);
} /* end of Cuddaux_addApply3 */

DdNode*
Cuddaux_addApplyN(struct opN* op,
		  DdNode** tab)
{
  DdNode *res;
  DdManager* dd = op->commonN.man->man;
  do {
    dd->reordered = 0;
    if (cuddauxCommonReinit(&op->commonN)==NULL) return NULL;
    res = cuddauxAddApplyNRecur(dd,op,tab);
  } while (dd->reordered == 1);
  return(res);
} /* end of Cuddaux_addApplyN */
DdNode*
Cuddaux_addApplyG(struct opG* op,
		  DdNode** tab)
{
  DdNode *res;
  DdManager* dd = op->commonG.man->man;
  do {
    dd->reordered = 0;
    if (cuddauxCommonReinit(&op->commonG)==NULL) return NULL;
    res = cuddauxAddApplyGRecur(dd,op,tab);
  } while (dd->reordered == 1);
  return(res);
} /* end of Cuddaux_addApplyG */

/**Function********************************************************************

  Synopsis:
	       exist(ite(var,cube,false),ite(var,f+,f-)) =
		 op(exist(cube,f+),exist(cube,f-))
	       exist(true,f) = f

  Assumptions:
	       op(f,f) = f,

  SideEffects [None

  Be careful to put a hook to reinitialize the table in case of reordering
  ]

  SeeAlso     []

******************************************************************************/
DdNode *
Cuddaux_addAbstract(struct exist* op,
		    DdNode * f,
		    DdNode * cube)

{
  DdNode *res;
  DdManager* dd = op->commonexist.man->man;

  if (bddCheckPositiveCube(dd, cube) == 0) {
    (void) fprintf(dd->err,
		   "Error: Can only abstract positive cubes\n");
    dd->errorCode = CUDD_INVALID_ARG;
    return(NULL);
  }
  do {
    dd->reordered = 0;
    if (cuddauxCommonReinit(&op->commonexist)==NULL ||
	cuddauxCommonReinit(&op->combineexist.common2)==NULL)
      return NULL;
    res = cuddauxAddAbstractRecur(dd,op,f,cube);
  } while (dd->reordered == 1);
  return(res);
} /* end of Cuddaux_addAbstract */

/**Function********************************************************************

  Synopsis:    exist(cube,op1(f))

	       existapply(ite(var,cube,false),ite(var,f+,f-)) =
		 op(existapply(cube,f+),existapply(cube,f-))
	       existapply(true,f) = op1 f


  Assumptions:
	       op(f,f) = f,

  SideEffects [None

  Be careful to put a hook to reinitialize the table in case of reordering
  ]

  SeeAlso     []

******************************************************************************/
DdNode *
Cuddaux_addApplyAbstract(struct existop1* op,
			 DdNode * f,
			 DdNode * cube)
{
  DdNode *res;
  DdManager* dd = op->commonexistop1.man->man;

  if (bddCheckPositiveCube(dd, cube) == 0) {
    (void) fprintf(dd->err,
		   "Error: Can only abstract positive cubes\n");
    dd->errorCode = CUDD_INVALID_ARG;
    return(NULL);
  }
  do {
    dd->reordered = 0;
    if (cuddauxCommonReinit(&op->commonexistop1)==NULL ||
	cuddauxCommonReinit(&op->combineexistop1.common2)==NULL ||
	cuddauxCommonReinit(&op->existop1.common1)==NULL)
      return NULL;
    res = cuddauxAddApplyAbstractRecur(dd,op,f,cube);
  } while (dd->reordered == 1);
  return(res);
} /* end of Cuddaux_addApplyAbstract */

/**Function********************************************************************

  Synopsis:    exist(cube,ite(f,g,background))

	       existand(ite(var,cube,false),ite(var,f+,f-),ite(var,g+,g-)) =
		 op(existand(cube,f+,g+),existand(cube,f-,g-)

	       existand(cube,true,g) = exist(cube,g)
	       existand(cube,false,g) = background

	       existand(true,f,g) = ite(f,g,background)

  Assumptions:
	       op(f,f) = f,
	       false AND f = background
	       true AND f = f

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode *
Cuddaux_addBddAndAbstract(struct existand* op,
			  DdNode * f, /* BDD */
			  DdNode * G, /* ADD */
			  DdNode * cube, /* BDD (cube) */
			  DdNode * background /* CST ADD */)
{
  DdNode *res;
  DdManager* dd = op->commonexistand.man->man;

  if (bddCheckPositiveCube(dd, cube) == 0) {
    (void) fprintf(dd->err,
		   "Error: Can only abstract positive cubes\n");
    dd->errorCode = CUDD_INVALID_ARG;
    return(NULL);
  }
  do {
    dd->reordered = 0;
    if (cuddauxCommonReinit(&op->commonexistand)==NULL ||
	cuddauxCommonReinit(&op->combineexistand.common2)==NULL)
      return NULL;
    res = cuddauxAddBddAndAbstractRecur(dd,op,f,G,cube,background);
  } while (dd->reordered == 1);
  return(res);
} /* end of Cuddaux_addApplyBddAndAbstract */

/**Function********************************************************************

  Synopsis:    exist(cube,ite(f,op1(g),background))

  Assumptions:
	       existop(f,f) = f,
	       false AND f = background
	       true AND f = f

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode *
Cuddaux_addApplyBddAndAbstract(struct existandop1* op,
			       DdNode * f, /* BDD */
			       DdNode * G, /* ADD */
			       DdNode * cube, /* BDD (cube) */
			       DdNode * background /* CST ADD */)
{
  DdNode *res;
  DdManager* dd = op->commonexistandop1.man->man;

  if (bddCheckPositiveCube(dd, cube) == 0) {
    (void) fprintf(dd->err,
		   "Error: Can only abstract positive cubes\n");
    dd->errorCode = CUDD_INVALID_ARG;
    return(NULL);
  }
  do {
    dd->reordered = 0;
    if (cuddauxCommonReinit(&op->commonexistandop1)==NULL ||
	cuddauxCommonReinit(&op->combineexistandop1.common2)==NULL ||
	cuddauxCommonReinit(&op->existandop1.common1)==NULL)
      return NULL;
    res = cuddauxAddApplyBddAndAbstractRecur(dd,op,f,G,cube,background);
  } while (dd->reordered == 1);
  return(res);
} /* end of Cuddaux_addApplyBddAndAbstract */

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cuddaux_addApply1.]

  Description [Performs the recursive step of Cuddaux_addApply1. Returns a
  pointer to the result if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     [cuddauxAddApply2Recur]

******************************************************************************/
DdNode *
cuddauxAddApply1Recur(DdManager * dd,
		      struct op1* op,
		      DdNode * f)
{
  DdNode *res, *ft, *fe, *T, *E;
  unsigned int index;

  statLine(dd);
  assert (f->ref>=1);

  /* Check cache. */
  res = cuddauxCommonLookup1(&op->common1,f);
  if (res != NULL) return res;

  /* Check terminal cases. */
  res = (op->funptr1)(dd,op,f);
  if (res != NULL) goto cuddauxAddApply1Recur_end;
  else if (cuddIsConstant(f)) return NULL;

  /* Recursive step. */
  index = f->index;
  ft = cuddT(f);
  fe = cuddE(f);

  T = cuddauxAddApply1Recur(dd,op,ft);
  if (T == NULL) return(NULL);
  cuddRef(T);

  E = cuddauxAddApply1Recur(dd,op,fe);
  if (E == NULL) {
    Cudd_RecursiveDeref(dd,T);
    return(NULL);
  }
  cuddRef(E);

  res = (T == E) ? T : cuddUniqueInter(dd,(int)index,T,E);
  if (res == NULL) {
    Cudd_RecursiveDeref(dd, T);
    Cudd_RecursiveDeref(dd, E);
    return(NULL);
  }
  cuddDeref(T);
  cuddDeref(E);

  /* Store result. */
 cuddauxAddApply1Recur_end:
  return cuddauxCommonInsert1(&op->common1,f,res);
} /* end of cuddauxAddApply1Recur */

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cudd_addApply2.]

  Description [Performs the recursive step of Cudd_addApply2. Returns a
  pointer to the result if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode *
cuddauxAddApply2Recur(DdManager * dd,
		      struct op2* op,
		      DdNode * f,
		      DdNode * g)
{
  DdNode *res,
    *fv, *fvn, *gv, *gvn,
    *T, *E;
  unsigned int ford, gord;
  unsigned int index;
  DD_CTFP cacheOp;

  statLine(dd);
  assert (f->ref>=1);
  assert (g->ref>=1);

  if (op->idempotent && f==g){
    return f;
  }
  if (op->commutative && f>g){
    DdNode* t = f; f=g; g=t;
  }
  /* Check cache. */
  res = cuddauxCommonLookup2(&op->common2,f,g);
  if (res != NULL) return res;

  /* Check terminal cases. */
  res = op->funptr2(dd,op,f,g);
  if (res != NULL) goto cuddauxAddApply2Recur_end;
  else if (cuddIsConstant(f) && cuddIsConstant(g)) return NULL;

  /* Recursive step. */
  ford = cuddI(dd,f->index);
  gord = cuddI(dd,g->index);
  if (ford <= gord) {
    index = f->index;
    fv = cuddT(f);
    fvn = cuddE(f);
  } else {
    index = g->index;
    fv = fvn = f;
  }
  if (gord <= ford) {
    gv = cuddT(g);
    gvn = cuddE(g);
  } else {
    gv = gvn = g;
  }

  T = cuddauxAddApply2Recur(dd,op,fv,gv);
  if (T == NULL) return(NULL);
  cuddRef(T);

  E = cuddauxAddApply2Recur(dd,op,fvn,gvn);
  if (E == NULL) {
    Cudd_RecursiveDeref(dd,T);
    return(NULL);
  }
  cuddRef(E);

  res = (T == E) ? T : cuddUniqueInter(dd,(int)index,T,E);
  if (res == NULL) {
    Cudd_RecursiveDeref(dd, T);
    Cudd_RecursiveDeref(dd, E);
    return(NULL);
  }
  cuddDeref(T);
  cuddDeref(E);

  /* Store result. */
 cuddauxAddApply2Recur_end:
  return cuddauxCommonInsert2(&op->common2,f,g,res);
} /* end of cuddauxAddApply2Recur */

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cudd_addTest2.]

  Description [Performs the recursive step of Cudd_addTest2. Returns a
  pointer to the result if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode *
cuddauxAddTest2Recur(DdManager * dd,
		     struct test2* op,
		     DdNode * f,
		     DdNode * g)
{
  DdNode *res,*one,
    *fv, *fvn, *gv, *gvn;
  unsigned int ford, gord;
  unsigned int index;
  DD_CTFP cacheOp;

  /* Check terminal cases. Op may swap f and g to increase the
   * cache hit rate.
   */
  statLine(dd);
  assert (f->ref>=1);
  assert (g->ref>=1);

  one = DD_ONE(dd);

  if (op->reflexive && f==g){
    return one;
  }
  if (op->symetric && f>g){
    DdNode* t = f; f=g; g=t;
  }
  /* Check cache. */
  res = cuddauxCommonLookup2(&op->common2t,f,g);
  if (res != NULL) return res;

  /* Check terminal cases. */
  res = op->funptr2t(dd,op,f,g);
  if (res != NULL)  goto cuddauxAddTest2Recur_end;
  else if (cuddIsConstant(f) && cuddIsConstant(g)) return NULL;

  /* Recursive step. */
  ford = cuddI(dd,f->index);
  gord = cuddI(dd,g->index);
  if (ford <= gord) {
    index = f->index;
    fv = cuddT(f);
    fvn = cuddE(f);
  } else {
    index = g->index;
    fv = fvn = f;
  }
  if (gord <= ford) {
    gv = cuddT(g);
    gvn = cuddE(g);
  } else {
    gv = gvn = g;
  }

  res = cuddauxAddTest2Recur(dd,op,fv,gv);
  if (res == NULL) return(NULL);
  if (res==one)
    res = cuddauxAddTest2Recur(dd,op,fvn,gvn);
  if (res==NULL) return NULL;

 cuddauxAddTest2Recur_end:
  return cuddauxCommonInsert2(&op->common2t,f,g,res);
} /* end of cuddauxAddTest2Recur */

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cuddaux_addApply3.]

  Description [Performs the recursive step of Cuddaux_addApply3. Returns a
  pointer to the result if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/

DdNode*
cuddauxAddApply3Recur(
  DdManager * dd,
  struct op3* op,
  DdNode * f,
  DdNode * g,
  DdNode * h
  )
{
    DdNode *res,
	   *fv, *fvn, *gv, *gvn, *hv, *hvn,
	   *T, *E;
    unsigned int ford, gord, hord, ghord, ord;
    unsigned int index;

    statLine(dd);
    assert (f->ref>=1);
    assert (g->ref>=1);
    assert (h->ref>=1);

    /* Check cache. */
    res = cuddauxCommonLookup3(&op->common3,f,g,h);
    if (res != NULL) return res;
    /* Check terminal cases. */
    res = op->funptr3(dd,op,f,g,h);
    if (res != NULL) goto cuddauxAddApply3Recur_end;
    else if (cuddIsConstant(f) && cuddIsConstant(g) && cuddIsConstant(h)) return NULL;

    /* Recursive step. */
    ford = cuddI(dd,f->index);
    gord = cuddI(dd,g->index);
    hord = cuddI(dd,h->index);
    ghord = ddMin(gord,hord);
    ord = ddMin(ford,ghord);
    index = -1;
    if (ford==ord){
      index = f-> index;
      fv = cuddT(f);
      fvn = cuddE(f);
    }
    else {
      fv = fvn = f;
    }
    if (gord==ord){
      index = g-> index;
      gv = cuddT(g);
      gvn = cuddE(g);
    }
    else {
      gv = gvn = g;
    }
    if (hord==ord){
      index = h-> index;
      hv = cuddT(h);
      hvn = cuddE(h);
    }
    else {
      hv = hvn = h;
    }
    T = cuddauxAddApply3Recur(dd,op,fv,gv,hv);
    if (T == NULL) return(NULL);
    cuddRef(T);

    E = cuddauxAddApply3Recur(dd,op,fvn,gvn,hvn);
    if (E == NULL) {
	Cudd_RecursiveDeref(dd,T);
	return(NULL);
    }
    cuddRef(E);

    res = (T == E) ? T : cuddUniqueInter(dd,(int)index,T,E);
    if (res == NULL) {
	Cudd_RecursiveDeref(dd, T);
	Cudd_RecursiveDeref(dd, E);
	return(NULL);
    }
    cuddDeref(T);
    cuddDeref(E);

    /* Do not keep the result if the reference count is only 1, since
    ** it will not be visited again.
    */
 cuddauxAddApply3Recur_end:
    return cuddauxCommonInsert3(&op->common3,f,g,h,res);
} /* end of cuddauxAddApply3Recur */

static inline unsigned int array_topindex(DdManager*dd, DdNode** tab, int size)
{
  int i;
  unsigned int index,level,leveli;

  index = CUDD_CONST_INDEX;
  level = CUDD_CONST_INDEX;
  for (i=0;i<size;i++){
    DdNode* f = Cudd_Regular(tab[i]);
    assert(f->ref>=1);
    unsigned int leveli = cuddI(dd,f->index);
    if (leveli < level){
      index = f->index;
      level = leveli;
    }
  }
  return index;
}
static inline void array_then(DdManager* dd,
			      DdNode** tab2,
			      DdNode** tab,
			      unsigned int index,
			      int sizeBdd, int size)
{
  int i;

  for (i=0;i<sizeBdd;i++){
    DdNode* f = Cudd_Regular(tab[i]);
    if (f->index==index){
      tab2[i] = cuddT(f);
      if (f!=tab[i]) tab2[i] = Cudd_Not(tab2[i]);
    }
    else {
      tab2[i] = tab[i];
    }
  }
  for (i=sizeBdd;i<size;i++){
    tab2[i] = (tab[i]->index==index) ? cuddT(tab[i]) : tab[i];
  }
}
static inline void array_else(DdManager* dd,
			      DdNode** tab2,
			      DdNode** tab,
			      unsigned int index,
			      int sizeBdd, int size)
{
  int i;

  for (i=0;i<sizeBdd;i++){
    DdNode* f = Cudd_Regular(tab[i]);
    if (f->index==index){
      tab2[i] = cuddE(f);
      if (f!=tab[i]) tab2[i] = Cudd_Not(tab2[i]);
    }
    else {
      tab2[i] = tab[i];
    }
  }
  for (i=sizeBdd;i<size;i++){
    tab2[i] = (tab[i]->index==index) ? cuddE(tab[i]) : tab[i];
  }
}

DdNode *
cuddauxAddApplyNRecur(DdManager * dd,
		      struct opN* op,
		      DdNode ** tab)
{
  DdNode *res,*T,*E;
  DdNode** tab2 = NULL;
  int i;
  unsigned int index;

  statLine(dd);

  const int size = op->commonN.arity;
  const int sizeBdd = op->arityNbdd;
  assert(sizeBdd<=size);

  /* Check cache. */
  res = cuddauxCommonLookupN(&op->commonN,tab);
  if (res != NULL) return res;

  /* Check terminal cases. */
  res = op->funptrN(dd,op,tab);
  if (res != NULL) goto cuddauxAddApplyNRecur_end;
  /* Compute top index */
  index = array_topindex(dd,tab,size);
  if (index==CUDD_CONST_INDEX) return NULL;
  /* Recursive step. */
  tab2 = malloc(size*sizeof(DdNode*));
  if (tab2==NULL) return NULL;
  array_then(dd,tab2,tab,index,sizeBdd,size);
  T = cuddauxAddApplyNRecur(dd,op,tab2);
  if (T == NULL){ free(tab2); return NULL; }
  cuddRef(T);

  array_else(dd,tab2,tab,index,sizeBdd,size);
  E = cuddauxAddApplyNRecur(dd,op,tab2);
  if (E == NULL){
    free(tab2);
    Cudd_RecursiveDeref(dd,T);
    return NULL;
  }
  cuddRef(E);
  free(tab2);

  res = (T == E) ? T : cuddUniqueInter(dd,(int)index,T,E);
  if (res == NULL) {
    Cudd_RecursiveDeref(dd, T);
    Cudd_RecursiveDeref(dd, E);
    return(NULL);
  }
  cuddDeref(T);
  cuddDeref(E);

  /* Store result. */
 cuddauxAddApplyNRecur_end:
  return cuddauxCommonInsertN(&op->commonN,tab,res);
}

DdNode *
cuddauxAddApplyGRecur(DdManager * dd,
		      struct opG* op,
		      DdNode ** tab)
{
  DdNode *res,*T,*E;
  DdNode** tab2 = NULL;
  int i;
  unsigned int index;

  statLine(dd);
  const int size = op->commonG.arity;
  const int sizeBdd = op->arityGbdd;
  assert(sizeBdd<=size);

  /* Check cache. */
  res = cuddauxCommonLookupN(&op->commonG,tab);
  if (res != NULL) return res;

  /* Check terminal cases. */
  res = op->funptrG(dd,op,tab);
  if (res != NULL) goto cuddauxAddApplyGRecur_end;

  /* Compute top index */
  index = array_topindex(dd,tab,size);
  if (index==CUDD_CONST_INDEX) return NULL;
  /* Recursive step: Then branch */
  tab2 = malloc(size*sizeof(DdNode*));
  if (tab2==NULL) return NULL;
  array_then(dd,tab2,tab,index,sizeBdd,size);
  if (op->funptrBeforeRec){
    if (!op->funptrBeforeRec(dd,op,dd->vars[index],tab2)){
      free(tab2); return NULL;
    }
    for (i=0;i<size;i++){
      cuddRef(tab2[i]);
    }
  }
  T = cuddauxAddApplyGRecur(dd,op,tab2);
  if (T != NULL) cuddRef(T);
  if (op->funptrBeforeRec){
    for (i=0;i<size;i++){
      Cudd_RecursiveDeref(dd,tab2[i]);
    }
  }
  if (T == NULL){ free(tab2); return NULL; }

  /* Recursive step: Else branch */
  array_else(dd,tab2,tab,index,sizeBdd,size);
  if (op->funptrBeforeRec){
    if (!op->funptrBeforeRec(dd,op,Cudd_Not(dd->vars[index]),tab2)){
      Cudd_RecursiveDeref(dd, T);
      free(tab2);
    }
    for (i=0;i<size;i++){
      cuddRef(tab2[i]);
    }
  }
  E = cuddauxAddApplyGRecur(dd,op,tab2);
  if (E != NULL) cuddRef(E);
  if (op->funptrBeforeRec){
    for (i=0;i<size;i++){
      Cudd_RecursiveDeref(dd,tab2[i]);
    }
  }
  free(tab2);
  if (E == NULL){
    Cudd_RecursiveDeref(dd,T);
    return NULL;
  }
  if (op->funptrIte){
    res = op->funptrIte(dd,op,index,T,E);
    if (res) cuddRef(res);
    Cudd_RecursiveDeref(dd, T);
    Cudd_RecursiveDeref(dd, E);
    if (res)
      cuddDeref(res);
    else
      return NULL;
  }
  else {
    res = cuddUniqueInter(dd,index,T,E);
    if (res == NULL) {
      Cudd_RecursiveDeref(dd, T);
      Cudd_RecursiveDeref(dd, E);
      return(NULL);
    }
    cuddDeref(T);
    cuddDeref(E);
  }

  /* Store result. */
 cuddauxAddApplyGRecur_end:
  return cuddauxCommonInsertN(&op->commonG,tab,res);
}

/**Function********************************************************************

  SideEffects [None]

  SeeAlso     [None]

******************************************************************************/
DdNode*
cuddauxAddAbstractRecur(DdManager * dd,
			struct exist* op,
			DdNode * G, /* ADD */
			DdNode * cube /* BDD (cube) */)
{
  DdNode *gt, *ge, *cube2;
  DdNode *one, *zero, *res, *T, *E;
  unsigned int topf, topcube, top, index;

  statLine(dd);
  one = DD_ONE(dd);
  zero = Cudd_Not(one);

  /* Terminal cases. */
  if (cube==one || cuddIsConstant(G)) return G;
  /* Here we can skip the use of cuddI, because the operands are known
  ** to be non-constant.
  */
  top = dd->perm[G->index];
  topcube = dd->perm[cube->index];

  while (topcube < top) {
    cube = cuddT(cube);
    if (cube == one) {
      return G;
    }
    topcube = dd->perm[cube->index];
  }
  /* Now, topcube >= top. */

  /* Check cache. */
  res = cuddauxCommonLookup2(&op->commonexist,G,cube);
  if (res != NULL) return res;

  gt = cuddT(G);
  ge = cuddE(G);

  /* If topcube == top, quantify, else just recurse */
  cube2 = (topcube == top) ? cuddT(cube) : cube;

  T = cuddauxAddAbstractRecur(dd, op, gt, cube2);
  if (T == NULL) return(NULL);
  /* If quantify: Special case: t==ge, implies that ge does not depend on the
     variables in Cube. One thus have
       ge OP (exist Cube ge) =
       ge OP ge =
       ge
    */
  if (topcube==top && T == ge) {
    res = ge;
    goto cuddauxAddAbstractRecur_end;
  }
  cuddRef(T);

  E = cuddauxAddAbstractRecur(dd, op, ge, cube2);
  if (E == NULL) {
    Cudd_RecursiveDeref(dd, T);
    return(NULL);
  }
  if (T == E){
    res = T;
    cuddDeref(T);
  }
  else {
    cuddRef(E);
    if (topcube == top) { /* quantify */
      res = cuddauxAddApply2Recur(dd,&op->combineexist,T,E);
      if (res == NULL) {
	Cudd_RecursiveDeref(dd, T);
	Cudd_RecursiveDeref(dd, E);
	return(NULL);
      }
      cuddRef(res);
      Cudd_RecursiveDeref(dd, T);
      Cudd_RecursiveDeref(dd, E);
      cuddDeref(res);
    }
    else { /* do not quantify */
      res = cuddUniqueInter(dd,(int)G->index,T,E);
      if (res == NULL) {
	Cudd_RecursiveDeref(dd, T);
	Cudd_RecursiveDeref(dd, E);
	return(NULL);
      }
      cuddDeref(T);
      cuddDeref(E);
    }
  }
 cuddauxAddAbstractRecur_end:
  return cuddauxCommonInsert2(&op->commonexist,G,cube,res);
} /* end of cuddauxAddAbstractRecur */

/**Function********************************************************************

  SideEffects [None]

  SeeAlso     [None]

******************************************************************************/
DdNode*
cuddauxAddApplyAbstractRecur(DdManager * dd,
			     struct existop1* op,
			     DdNode * G, /* ADD */
			     DdNode * cube /* BDD (cube) */)
{
  DdNode *gt, *ge, *cube2;
  DdNode *one, *zero, *res, *T, *E;
  unsigned int topf, topcube, top, index;

  statLine(dd);
  one = DD_ONE(dd);
  zero = Cudd_Not(one);

  /* Terminal cases. */
  if (cube==one || cuddIsConstant(G)){
    return cuddauxAddApply1Recur(dd,&op->existop1,G);
  }
  /* Here we can skip the use of cuddI, because the operands are known
  ** to be non-constant.
  */
  top = dd->perm[G->index];
  topcube = dd->perm[cube->index];

  while (topcube < top) {
    cube = cuddT(cube);
    if (cube == one) {
      return cuddauxAddApply1Recur(dd,&op->existop1,G);
    }
    topcube = dd->perm[cube->index];
  }
  /* Now, topcube >= top. */

  /* Check cache. */
  res = cuddauxCommonLookup2(&op->commonexistop1,G,cube);
  if (res != NULL) return res;

  gt = cuddT(G);
  ge = cuddE(G);

  /* If topcube == top, quantify, else just recurse */
  cube2 = (topcube == top) ? cuddT(cube) : cube;

  T = cuddauxAddApplyAbstractRecur(dd, op, gt, cube2);
  if (T == NULL) return(NULL);
  /* If quantify: Special case: t==ge, implies that ge does not depend on the
     variables in Cube. One thus have
       ge OP (exist Cube ge) =
       ge OP ge =
       ge
    */
  if (topcube==top && T == ge) {
    res = ge;
    goto cuddauxAddApplyAbstractRecur_end;
  }
  cuddRef(T);

  E = cuddauxAddApplyAbstractRecur(dd, op, ge, cube2);
  if (E == NULL) {
    Cudd_RecursiveDeref(dd, T);
    return(NULL);
  }
  if (T == E){
    res = T;
    cuddDeref(T);
  }
  else {
    cuddRef(E);
    if (topcube == top) { /* quantify */
      res = cuddauxAddApply2Recur(dd,&op->combineexistop1,T,E);
      if (res == NULL) {
	Cudd_RecursiveDeref(dd, T);
	Cudd_RecursiveDeref(dd, E);
	return(NULL);
      }
      cuddRef(res);
      Cudd_RecursiveDeref(dd, T);
      Cudd_RecursiveDeref(dd, E);
      cuddDeref(res);
    }
    else { /* do not quantify */
      res = cuddUniqueInter(dd,(int)G->index,T,E);
      if (res == NULL) {
	Cudd_RecursiveDeref(dd, T);
	Cudd_RecursiveDeref(dd, E);
	return(NULL);
      }
      cuddDeref(E);
      cuddDeref(T);
    }
  }
 cuddauxAddApplyAbstractRecur_end:
  return cuddauxCommonInsert2(&op->commonexistop1,G,cube,res);
} /* end of cuddauxAddApplyAbstractRecur */

/**Function********************************************************************

  SideEffects [None]

  SeeAlso     [None]

******************************************************************************/
DdNode*
cuddauxAddBddAndAbstractRecur(DdManager * dd,
			      struct existand* op,
			      DdNode * f, /* BDD */
			      DdNode * G, /* ADD */
			      DdNode * cube, /* BDD (cube) */
			      DdNode * background /* CST ADD */)
{
  DdNode *F, *ft, *fe, *gt, *ge, *cube2;
  DdNode *one, *zero, *res, *T, *E;
  unsigned int topf, topg, topcube, top, index;

  statLine(dd);
  one = DD_ONE(dd);
  zero = Cudd_Not(one);

  /* Terminal cases. */
  if (f==zero || G==background) return background;
  if (cube==one) return cuddauxAddIteRecur(dd,f,G,background);
  if (cuddIsConstant(G)){
    DdNode* res1 = cuddBddExistAbstractRecur(dd,f,cube);
    if (res1==NULL) return NULL;
    cuddRef(res1);
    DdNode* res = cuddauxAddIteRecur(dd,res1,G,background);
    Cudd_IterDerefBdd(dd,res1);
    return res;
  }
  /* f may still be constant one !
   */
  F = Cudd_Regular(f);
  topf = (f==one) ? (int)CUDD_CONST_INDEX : dd->perm[F->index];
  topg = dd->perm[G->index];
  top = ddMin(topf, topg);
  topcube = dd->perm[cube->index];

  while (topcube < top) {
    cube = cuddT(cube);
    if (cube == one) {
      return cuddauxAddIteRecur(dd,f,G,background);
    }
    topcube = dd->perm[cube->index];
  }
  /* Now, topcube >= top. */

  /* Check cache. */
  res = cuddauxCommonLookup3(&op->commonexistand,f,G,cube);
  if (res != NULL) return res;

  /* Decompose */
  if (topf == top) {
    index = F->index;
    ft = cuddT(F);
    fe = cuddE(F);
    if (Cudd_IsComplement(f)) {
      ft = Cudd_Not(ft);
      fe = Cudd_Not(fe);
    }
  } else {
    index = G->index;
    ft = fe = f;
  }
  if (topg == top) {
    gt = cuddT(G);
    ge = cuddE(G);
  } else {
    gt = ge = G;
  }

  /* If topcube == top, quantify, else just recurse */
  cube2 = (topcube == top) ? cuddT(cube) : cube;

  T = cuddauxAddBddAndAbstractRecur(dd, op, ft, gt, cube2, background);
  if (T == NULL) return(NULL);
  /* If quantifiy: special case: t==ge, implies that ge does not depend on the
       variables in Cube. One thus have
       ge OP (exist cube (fe and ge)) =
       ge OP ite(exist fe,ge,background) =
       ite(exist fe,ge EXISTOP ge,ge EXISTOP background =
       ge
    */
  if (topcube==top && T == ge) {
    res = ge;
    goto cuddauxAddBddAndAbstractRecur_end;
  }
  cuddRef(T);
  E = cuddauxAddBddAndAbstractRecur(dd, op, fe, ge, cube2, background);
  if (E == NULL) {
    Cudd_RecursiveDeref(dd, T);
    return(NULL);
  }
  if (E == NULL) return(NULL);
  if (T == E || (topcube==top && E==background)){
    res = T;
    cuddDeref(T);
  }
  else if (topcube==top && T==background){
    res = E;
    Cudd_RecursiveDeref(dd, T);
  }
  else {
    cuddRef(E);
    if (topcube == top) { /* quantify */
      res = cuddauxAddApply2Recur(dd,&op->combineexistand,T,E);
      if (res == NULL) {
	Cudd_RecursiveDeref(dd, T);
	Cudd_RecursiveDeref(dd, E);
	return(NULL);
      }
      cuddRef(res);
      Cudd_RecursiveDeref(dd, T);
      Cudd_RecursiveDeref(dd, E);
      cuddDeref(res);
    }
    else { /* recurse */
      res = cuddUniqueInter(dd,(int)G->index,T,E);
      if (res == NULL) {
	Cudd_RecursiveDeref(dd, T);
	Cudd_RecursiveDeref(dd, E);
	return(NULL);
      }
      cuddDeref(E);
      cuddDeref(T);
    }
  }
 cuddauxAddBddAndAbstractRecur_end:
  return cuddauxCommonInsert3(&op->commonexistand,f,G,cube,res);
} /* end of cuddauxAddBddAndAbstractRecur */

/**Function********************************************************************

  SideEffects [None]

  SeeAlso     [None]

******************************************************************************/
DdNode*
cuddauxAddApplyBddAndAbstractRecur(DdManager * dd,
				   struct existandop1* op,
				   DdNode * f, /* BDD */
				   DdNode * G, /* ADD */
				   DdNode * cube, /* BDD (cube) */
				   DdNode * background /* CST ADD */)
{
  DdNode *F, *ft, *fe, *gt, *ge, *cube2;
  DdNode *one, *zero, *res, *T, *E;
  unsigned int topf, topg, topcube, top, index;

  statLine(dd);
  one = DD_ONE(dd);
  zero = Cudd_Not(one);

  /* Terminal cases. */
  if (f==zero) return background;
  if (f==one && cube==one){
    return cuddauxAddApply1Recur(dd,&op->existandop1,G);
  }
  if (cuddIsConstant(G)){
    G = cuddauxAddApply1Recur(dd,&op->existandop1,G);
    if (G==background) return background;
    if (cube==one){
      return cuddauxAddIteRecur(dd,f,G,background);
    }
    else {
      DdNode* res1 = cuddBddExistAbstractRecur(dd,f,cube);
      if (res1==NULL) return NULL;
      cuddRef(res1);
      DdNode* res = cuddauxAddIteRecur(dd,res1,G,background);
      Cudd_IterDerefBdd(dd,res1);
      return res;
    }
  }
  /* f,cube may still be constant one ! */
  F = Cudd_Regular(f);
  topf = (f==one) ? (int)CUDD_CONST_INDEX : dd->perm[F->index];
  topg = dd->perm[G->index];
  top = ddMin(topf, topg);
  topcube = dd->perm[cube->index];

  while (topcube < top) {
    cube = cuddT(cube);
    if (cube == one) {
      G = cuddauxAddApply1Recur(dd,&op->existandop1,G);
      if (G==background) return background;
      return cuddauxAddIteRecur(dd,f,G,background);
    }
    topcube = dd->perm[cube->index];
  }
  /* Now, topcube >= top. */

  /* Check cache. */
  res = cuddauxCommonLookup3(&op->commonexistandop1,f,G,cube);
  if (res != NULL) return res;

  /* Decompose */
  if (topf == top) {
    index = F->index;
    ft = cuddT(F);
    fe = cuddE(F);
    if (Cudd_IsComplement(f)) {
      ft = Cudd_Not(ft);
      fe = Cudd_Not(fe);
    }
  } else {
    index = G->index;
    ft = fe = f;
  }
  if (topg == top) {
    gt = cuddT(G);
    ge = cuddE(G);
  } else {
    gt = ge = G;
  }

  /* If topcube == top, quantify, else just recurse */
  cube2 = (topcube == top) ? cuddT(cube) : cube;

  T = cuddauxAddApplyBddAndAbstractRecur(dd, op, ft, gt, cube2, background);
  if (T == NULL) return(NULL);
  cuddRef(T);
  E = cuddauxAddApplyBddAndAbstractRecur(dd, op, fe, ge, cube2, background);
  if (E == NULL) {
    Cudd_RecursiveDeref(dd, T);
    return(NULL);
  }
  if (E == NULL) return(NULL);
  if (T == E || (topcube==top && E==background)){
    res = T;
    cuddDeref(T);
  }
  else if (topcube==top && T==background){
    res = E;
    Cudd_RecursiveDeref(dd, T);
  }
  else {
    cuddRef(E);
    if (topcube == top) { /* quantify */
      res = cuddauxAddApply2Recur(dd,&op->combineexistandop1,T,E);
      if (res == NULL) {
	Cudd_RecursiveDeref(dd, T);
	Cudd_RecursiveDeref(dd, E);
	return(NULL);
      }
      cuddRef(res);
      Cudd_RecursiveDeref(dd, T);
      Cudd_RecursiveDeref(dd, E);
      cuddDeref(res);
    }
    else { /* recurse */
      res = cuddUniqueInter(dd,(int)G->index,T,E);
      if (res == NULL) {
	Cudd_RecursiveDeref(dd, T);
	Cudd_RecursiveDeref(dd, E);
	return(NULL);
      }
      cuddDeref(E);
      cuddDeref(T);
    }
  }
 cuddauxAddApplyBddAndAbstractRecur_end:
  return cuddauxCommonInsert3(&op->commonexistandop1,f,G,cube,res);
} /* end of cuddauxAddApplyBddAndAbstractRecur */

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis [Checks whether cube is an BDD representing the product of
  positive literals.]

  Description [Returns 1 in case of success; 0 otherwise.]

  SideEffects [None]

******************************************************************************/
static int
bddCheckPositiveCube(
  DdManager * dd,
  DdNode * cube)
{
    if (Cudd_IsComplement(cube)) return(0);
    if (cube == DD_ONE(dd)) return(1);
    if (cuddIsConstant(cube)) return(0);
    if (cuddE(cube) == Cudd_Not(DD_ONE(dd))) {
	return(bddCheckPositiveCube(dd, cuddT(cube)));
    }
    return(0);

} /* end of bddCheckPositiveCube */
