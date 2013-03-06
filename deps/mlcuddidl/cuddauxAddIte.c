/* $Id: cuddauxAddIte.c,v 1.2 2005/06/14 14:37:56 bjeannet Exp $ */

/**CFile***********************************************************************

  FileName    [cuddauxAddIte.c]

  PackageName [cuddaux]

  Synopsis    [ADD ITE function and satellites, taking BDDs as arguments (instead of a 0-1 ADD as in cuddAddIte.c)]

  Description [External procedures included in this module:
		<ul>
		<li> Cuddaux_addIte()
		<li> Cuddaux_addBddAnd()
		<li> Cuddaux_addIteConstant()
		<li> Cuddaux_addEvalConst()
		</ul>
	Internal procedures included in this module:
		<ul>
		<li> cuddauxAddIteRecur()
		<li> cuddauxAddBddAndRecur()
		</ul>
	Static procedures included in this module:
		<ul>
		</ul>]

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

  Synopsis    [Implements ITE(f,g,h).]

  Description [Implements ITE(f,g,h). This procedure assumes that f is
  a BDD. Returns a pointer to the resulting ADD if successful; NULL
  otherwise.]

  SideEffects [None]

  SeeAlso     [Cudd_addIte Cudaux_addBddAnd]

******************************************************************************/
DdNode*
Cuddaux_addIte(
  DdManager* dd,
  DdNode* f,
  DdNode* g,
  DdNode* h)
{
  DdNode *res;

  do {
    dd->reordered = 0;
    res = cuddauxAddIteRecur(dd,f,g,h);
    } while (dd->reordered == 1);
  return(res);
} /* end of Cuddaux_addIte */


/**Function********************************************************************

  Synopsis    [Implements ITE(f,g,background).]

  Description [Implements ITE(f,g,background). This procedure assumes that f is
  a BDD. Returns a pointer to the resulting ADD if successful; NULL
  otherwise.]

  SideEffects [None]

  SeeAlso     [Cuddaux_addIte]
******************************************************************************/
DdNode *
Cuddaux_addBddAnd(
  DdManager * dd,
  DdNode * f,
  DdNode * g)
{
  DdNode *res;
  
  do {
    dd->reordered = 0;
    res = cuddauxAddBddAndRecur(dd,f,g);
  } while (dd->reordered == 1);
  return(res);
    
} /* end of Cudd_addBddAnd */

/**Function********************************************************************

  Synopsis    [Implements ITEconstant for ADDs.]

  Description [Implements ITEconstant for ADDs.  f must be a BDD.
  Returns a pointer to the resulting ADD (which may or may not be
  constant) or DD_NON_CONSTANT. No new nodes are created. This function
  can be used, for instance, to check that g has a constant value
  (specified by h) whenever f is 1. If the constant value is unknown,
  then one should use Cudd_addEvalConst.]

  SideEffects [None]

  SeeAlso     [Cudd_addIteConstant]

******************************************************************************/
DdNode *
Cuddaux_addIteConstant(
  DdManager * dd,
  DdNode * f,
  DdNode * g,
  DdNode * h)
{
  DdNode *one,*zero;
  DdNode *Fv,*Fnv,*Gv,*Gnv,*Hv,*Hnv,*r,*t,*e;
  unsigned int topf,topg,toph,top;
  
  /* Trivial cases. */
  one = DD_ONE(dd);
  zero = Cudd_Not(one);
 
  if (f == one) {	/* ITE(1,G,H) = G */
    return(g);
  }
  if (f == zero){	/* ITE(0,G,H) = H */
    return(h);
  }
  
  /* Check remaining one variable cases. */
  if (g == h) { 			/* ITE(F,G,G) = G */
    return(g);
  }
  if (cuddIsConstant(g) && cuddIsConstant(h)) {
    return(DD_NON_CONSTANT);
  }
  
  /* Put into canonical form */
  if (Cudd_IsComplement(f)){
    DdNode* t = g; g = h; h = t;
    f = Cudd_Not(f);
  }
  topf = cuddI(dd,f->index);
  topg = cuddI(dd,g->index);
  toph = cuddI(dd,h->index);
  top = ddMin(topg,toph);
  
  /* ITE(F,G,H) = (x,G,H) (non constant) if F = (x,1,0), x < top(G,H). */
  if (topf < top && cuddT(f) == one && cuddE(f) == zero) {
    return(DD_NON_CONSTANT);
  }
  
  /* Check cache. */
  r = cuddConstantLookup(dd,DDAUX_ADD_ITE_CONSTANT_TAG,f,g,h);
  if (r != NULL) {
    return(r);
  }
  
  /* Compute cofactors. */
  top = ddMin(topf,top);
  if (topf == top) {
    Fv = cuddT(f); Fnv = cuddE(f);
  } else {
    Fv = Fnv = f;
  }
  if (topg == top) {
    Gv = cuddT(g); Gnv = cuddE(g);
  } else {
    Gv = Gnv = g;
  }
  if (toph == top) {
    Hv = cuddT(h); Hnv = cuddE(h);
  } else {
    Hv = Hnv = h;
  }
  
  /* Recursive step. */
  t = Cuddaux_addIteConstant(dd,Fv,Gv,Hv);
  if (t == DD_NON_CONSTANT || !cuddIsConstant(t)) {
    cuddCacheInsert(dd, DDAUX_ADD_ITE_CONSTANT_TAG, f, g, h, DD_NON_CONSTANT);
    return(DD_NON_CONSTANT);
  }
  e = Cuddaux_addIteConstant(dd,Fnv,Gnv,Hnv);
  if (e == DD_NON_CONSTANT || !cuddIsConstant(e) || t != e) {
    cuddCacheInsert(dd, DDAUX_ADD_ITE_CONSTANT_TAG, f, g, h, DD_NON_CONSTANT);
    return(DD_NON_CONSTANT);
  }
  cuddCacheInsert(dd, DDAUX_ADD_ITE_CONSTANT_TAG, f, g, h, t);
  return(t);
  
} /* end of Cuddaux_addIteConstant */

/**Function********************************************************************

  Synopsis    [Checks whether ADD g is constant whenever BDD f is 1.]

  Description [Checks whether ADD g is constant whenever BDD f is 1.  f
  must be a BDD.  Returns a pointer to the resulting ADD (which may
  or may not be constant) or DD_NON_CONSTANT. If f is identically 0,
  the check is assumed to be successful, and the background value is
  returned. No new nodes are created.]

  SideEffects [None]

  SeeAlso     [Cudd_addEvalConst]

******************************************************************************/
DdNode *
Cuddaux_addEvalConst(
  DdManager * dd,
  DdNode * f,
  DdNode * g)
{
  DdNode *one,*zero;
  DdNode *F,*Fv,*Fnv,*Gv,*Gnv,*r,*t,*e;
  unsigned int topf,topg;

#ifdef DD_DEBUG
  assert(!Cudd_IsComplement(f));
#endif

  /* Trivial cases. */
  one = DD_ONE(dd);
  zero = Cudd_Not(one);
 
  if (f == one || cuddIsConstant(g)) {
    return(g);
  }
  if (f == zero) {
    return(DD_BACKGROUND(dd));
  }
  F = Cudd_Regular(f);
#ifdef DD_DEBUG
  assert(!cuddIsConstant(F));
#endif
  /* Check cache. */
  r = cuddCacheLookup2(dd, Cuddaux_addEvalConst ,f, g);
  if (r != NULL) {
    return(r);
  }

  /* From now on, f and g are known not to be constants. */
  topf = cuddI(dd,F->index);
  topg = cuddI(dd,g->index);

  /* Compute cofactors. */
  if (topf <= topg) {
    Fv = cuddT(F); Fnv = cuddE(F);
    if (Cudd_IsComplement(f)) {
      Fv = Cudd_Not(Fv); 
      Fnv = Cudd_Not(Fnv);
    }
  } else {
    Fv = Fnv = f;
  }
  if (topg <= topf) {
    Gv = cuddT(g); Gnv = cuddE(g);
  } else {
    Gv = Gnv = g;
  }
    
  /* Recursive step. */
  if (Fv != zero) {
    t = Cuddaux_addEvalConst(dd,Fv,Gv);
    if (t == DD_NON_CONSTANT || !cuddIsConstant(t)) {
      cuddCacheInsert2(dd, Cuddaux_addEvalConst, f, g, DD_NON_CONSTANT);
      return(DD_NON_CONSTANT);
    }
    if (Fnv != zero) {
      e = Cuddaux_addEvalConst(dd,Fnv,Gnv);
      if (e == DD_NON_CONSTANT || !cuddIsConstant(e) || t != e) {
	cuddCacheInsert2(dd, Cuddaux_addEvalConst, f, g, DD_NON_CONSTANT);
	return(DD_NON_CONSTANT);
      }
    }
    cuddCacheInsert2(dd,Cuddaux_addEvalConst,f,g,t);
    return(t);
  } else { /* Fnv must be != zero */
    e = Cuddaux_addEvalConst(dd,Fnv,Gnv);
    cuddCacheInsert2(dd, Cuddaux_addEvalConst, f, g, e);
    return(e);
  }

} /* end of Cuddaux_addEvalConst */

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Implements the recursive step of Cuddaux_addIte(f,g,h).]

  Description [Implements the recursive step of Cudd_addIte(f,g,h).
  Returns a pointer to the resulting ADD if successful; NULL
  otherwise.]

  SideEffects [None]

  SeeAlso     [Cuddaux_addIte]

******************************************************************************/
DdNode *
cuddauxAddIteRecur(
  DdManager * dd,
  DdNode * f,
  DdNode * g,
  DdNode * h)
{
  DdNode *one,*zero;
  DdNode *r,*Fv,*Fnv,*Gv,*Gnv,*Hv,*Hnv,*t,*e;
  unsigned int topf,topg,toph,topgh,v;
  int index=-1;

  /* Trivial cases. */
  one = DD_ONE(dd);
  zero = Cudd_Not(one);
    
  /* One variable cases. */
  if (f == one) {	/* ITE(1,G,H) = G */
    return(g);
  }
  if (f == zero) {	/* ITE(0,G,H) = H */
    return(h);
  }
  if (g == h) {         /* ITE(F,G,G) = F */
    return(g);
  }
  if (h==DD_BACKGROUND(dd)){
    return (cuddauxAddBddAndRecur(dd,f,g));
  }
  if (g==DD_BACKGROUND(dd)){
    return (cuddauxAddBddAndRecur(dd,Cudd_Not(f),h));
  }

  /* Put into canonical form */
  if (Cudd_IsComplement(f)){
    DdNode* t = g; g = h; h = t;
    f = Cudd_Not(f);
  }

  /* From now on, f is known to not be a constant. */
  topf = cuddI(dd,f->index);
  topg = cuddI(dd,g->index);
  toph = cuddI(dd,h->index);
  topgh = ddMin(topg,toph);


  /* A shortcut: ITE(F,G,H) = (x,G,H) if F=(x,1,0), x < top(G,H). */
  if (topf < topgh && cuddT(f) == one && cuddE(f) == zero) {
    r = cuddUniqueInter(dd,(int)f->index,g,h);
    return(r);
  }

  /* Check cache. */
  r = cuddCacheLookup(dd,DDAUX_ADD_ITE_TAG,f,g,h);
  if (r != NULL) {
    return(r);
  }

  /* Compute cofactors. */
  v = ddMin(topf,topgh);
  if (topf == v) {
    index = f->index;
    Fv = cuddT(f); Fnv = cuddE(f);
  } else {
    Fv = Fnv = f;
  }
  if (topg == v) {
    index = g->index;
    Gv = cuddT(g); Gnv = cuddE(g);
  } else {
    Gv = Gnv = g;
  }
  if (toph == v) {
    index = h->index;
    Hv = cuddT(h); Hnv = cuddE(h);
  } else {
    Hv = Hnv = h;
  }

  /* Recursive step. */
  t = cuddauxAddIteRecur(dd,Fv,Gv,Hv);
  if (t == NULL) return(NULL);
  cuddRef(t);
  
  e = cuddauxAddIteRecur(dd,Fnv,Gnv,Hnv);
  if (e == NULL) {
    Cudd_RecursiveDeref(dd,t);
    return(NULL);
  }
  cuddRef(e);

  r = (t == e) ? t : cuddUniqueInter(dd,index,t,e);
  if (r == NULL) {
    Cudd_RecursiveDeref(dd,t);
    Cudd_RecursiveDeref(dd,e);
    return(NULL);
  }
  cuddDeref(t);
  cuddDeref(e);

  cuddCacheInsert(dd,DDAUX_ADD_ITE_TAG,f,g,h,r);

  return(r);
  
} /* end of cuddauxAddIteRecur */

/**Function********************************************************************

  Synopsis    [Implements the recursive step of Cuddaux_addBddAnd(f,g).]

  Description [Implements the recursive step of Cuddaux_addBddAnd(f,g).
  Returns a pointer to the resulting ADD if successful; NULL
  otherwise.]

  SideEffects [None]

  SeeAlso     [Cuddaux_addBddAnd]

******************************************************************************/
DdNode *
cuddauxAddBddAndRecur(
  DdManager * dd,
  DdNode * f,
  DdNode * g)
{
  DdNode *one,*zero;
  DdNode *F, *r,*Fv,*Fnv,*Gv,*Gnv,*t,*e;
  unsigned int topf,topg,v;
  int index=-1;

  /* Trivial cases. */
  one = DD_ONE(dd);
  zero = Cudd_Not(one);
    
  if (f == one) {
    return(g);
  }
  if (f == zero || g == DD_BACKGROUND(dd)) {
    return(DD_BACKGROUND(dd));
  }

  F = Cudd_Regular(f);
  Fv = cuddT(F); Fnv = cuddE(F);
  if (Cudd_IsComplement(f)){
    Fv = Cudd_Not(Fv); Fnv = Cudd_Not(Fnv);
  }
  
  /* From now on, f is known to not be a constant. */
  topf = cuddI(dd,F->index);
  topg = cuddI(dd,g->index);

  /* A shortcut: ITE(F,G,back) = (x,G,back) if F=(x,1,0), x < top(G). */
  if (topf < topg && Fv == one && Fnv == zero) {
    r = cuddUniqueInter(dd,(int)F->index,g,DD_BACKGROUND(dd));
    return(r);
  }
  if (topf < topg && Fv == zero && Fnv == one) {
    r = cuddUniqueInter(dd,(int)F->index,DD_BACKGROUND(dd),g);
    return(r);
  }

  /* Check cache. */
  r = cuddCacheLookup2(dd,Cuddaux_addBddAnd,f,g);
  if (r != NULL) {
    return(r);
  }

  /* Compute cofactors. */
  v = ddMin(topf,topg);/* v = top_var(F,G) */
  if (topf == v) {
    index = F->index;
    /* Fv and Fnv already computed */
  } else {
    Fv = Fnv = f;
  }
  if (topg == v) {
    index = g->index;
    Gv = cuddT(g); Gnv = cuddE(g);
  } else {
    Gv = Gnv = g;
  }

  /* Recursive step. */
  t = cuddauxAddBddAndRecur(dd,Fv,Gv);
  if (t == NULL) return(NULL);
  cuddRef(t);
  
  e = cuddauxAddBddAndRecur(dd,Fnv,Gnv);
  if (e == NULL) {
    Cudd_RecursiveDeref(dd,t);
    return(NULL);
  }
  cuddRef(e);

  r = (t == e) ? t : cuddUniqueInter(dd,index,t,e);
  if (r == NULL) {
    Cudd_RecursiveDeref(dd,t);
    Cudd_RecursiveDeref(dd,e);
    return(NULL);
  }
  cuddDeref(t);
  cuddDeref(e);

  if (F->ref != 1 || g->ref != 1)
    cuddCacheInsert2(dd,Cuddaux_addBddAnd,f,g,r);
  
  return(r);
  
} /* end of cuddauxAddBddAndRecur */

