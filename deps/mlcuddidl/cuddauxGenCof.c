/* $Id: cuddauxGenCof.c,v 1.1.1.1 2002/05/14 13:04:04 bjeannet Exp $ */

/**CFile***********************************************************************

  FileName    [cuddauxGenCof.c]

  PackageName [cuddaux]

  Synopsis    [Generalized cofactors for BDDs and ADDs.]

  Description [Modified versions of some functions in cuddGenCof.c.
            bddRestrict does not test any more the size of the result.
            0-1 ADDs are replaced by BDDs.]

            External procedures included in this module:
		<ul>
		<li> Cuddaux_bddRestrict()
		<li> Cuddaux_addRestrict()
		<li> Cuddaux_addConstrain()
		</ul>
	    Internal procedures included in this module:
		<ul>
		<li> cuddauxAddRestrictRecur()
		<li> cuddauxAddConstrainRecur()
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

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis [BDD restrict according to Coudert and Madre's algorithm
  (ICCAD90).]

  Description [BDD restrict according to Coudert and Madre's algorithm
  (ICCAD90). Returns the restricted BDD if successful; otherwise NULL.]

  SideEffects [None]

  SeeAlso     [Cudd_bddRestrict]

******************************************************************************/
DdNode*
Cuddaux_bddRestrict(DdManager * dd, DdNode * f, DdNode * c)
{
  DdNode *one,*zero;
  DdNode *suppF, *suppC, *commonSupp, *onlyC;
  DdNode *cplus, *res;
  int retval;
  
  one = DD_ONE(dd);
  zero = Cudd_Not(one);
  /* Check terminal cases here to avoid computing supports in trivial cases.
  ** This also allows us notto check later for the case c == 0, in which
  ** there is no common support. */
  if (c == one) return(f);
  if (c == zero){
    fprintf(stderr,"Cuddaux_bddRestrict: warning: false careset\n");
    return(zero);
  }
  if (Cudd_IsConstant(f)) return(f);
  if (f == c) return(one);
  if (f == Cudd_Not(c)) return(zero);
  
  /* Check if supports intersect. */
  suppF = Cuddaux_Support(dd,f);
  if (suppF==NULL) return(NULL);
  cuddRef(suppF);

  suppC = Cuddaux_Support(dd,c);
  if (suppC==NULL){
    Cudd_IterDerefBdd(dd,suppF);
    return(NULL);
  }
  cuddRef(suppC);

  commonSupp = Cudd_bddLiteralSetIntersection(dd,suppF,suppC);
  if (commonSupp==NULL){
    Cudd_IterDerefBdd(dd,suppF);
    Cudd_IterDerefBdd(dd,suppC); 
    return(NULL);
  }
  if (commonSupp == one) {
    Cudd_IterDerefBdd(dd,suppF);
    Cudd_IterDerefBdd(dd,suppC); 
    return(f);
  }
  cuddRef(commonSupp);

  Cudd_IterDerefBdd(dd,suppF);
  /* Abstract from c the variables that do not appear in f. */
  onlyC = Cudd_Cofactor(dd,suppC,commonSupp);
  if (onlyC == NULL) {
    Cudd_IterDerefBdd(dd,suppC); 
    Cudd_IterDerefBdd(dd,commonSupp); 
    return(NULL);
  }
  cuddRef(onlyC);
  Cudd_IterDerefBdd(dd,suppC); 
  Cudd_IterDerefBdd(dd,commonSupp); 
  cplus = Cudd_bddExistAbstract(dd, c, onlyC);
  if (cplus == NULL) {
    Cudd_IterDerefBdd(dd,onlyC); 
    return(NULL);
  }
  cuddRef(cplus);
  Cudd_IterDerefBdd(dd,onlyC);
  
  do {
    dd->reordered = 0;
    res = cuddBddRestrictRecur(dd, f, cplus);
  } while (dd->reordered == 1);
  if (res == NULL) {
    Cudd_IterDerefBdd(dd,cplus);
    return(NULL);
  }
  cuddRef(res);
  Cudd_IterDerefBdd(dd,cplus);
  cuddDeref(res);
  return(res);
} /* end of Cuddaux_bddRestrict */

/**Function********************************************************************

  Synopsis [ADD restrict according to Coudert and Madre's algorithm
  (ICCAD90).]

  Description [ADD restrict according to Coudert and Madre's algorithm
  (ICCAD90). f is an ADD, g a BDD. 
  Returns the restricted ADD if successful; otherwise NULL.]

  SideEffects [None]

  SeeAlso     [Cudd_addRestrict]

******************************************************************************/
DdNode*
Cuddaux_addRestrict(DdManager* dd, DdNode* f, DdNode* c)
{
  DdNode *one,*zero;
  DdNode *suppF, *suppC, *commonSupp, *onlyC;
  DdNode *cplus, *res;
  int retval;
  
  one = DD_ONE(dd);
  zero = Cudd_Not(one);
  /* Check terminal cases here to avoid computing supports in trivial cases.
  ** This also allows us notto check later for the case c == 0, in which
  ** there is no common support. */
  if (c == one) return f;
  if (c == zero){
    fprintf(stderr,"Cuddaux_addRestrict: warning: false careset\n");
    return(DD_BACKGROUND(dd));
  }
  if (Cudd_IsConstant(f)) return(f);
  
  /* Check if supports intersect. */
  suppF = Cuddaux_Support(dd,f);
  if (suppF==NULL) return(NULL);
  cuddRef(suppF);
  suppC = Cuddaux_Support(dd,c);
  if (suppC==NULL){
    Cudd_IterDerefBdd(dd,suppF);
    return(NULL);
  }
  cuddRef(suppC);
  commonSupp = Cudd_bddLiteralSetIntersection(dd,suppF,suppC);
  if (commonSupp==NULL){
    Cudd_IterDerefBdd(dd,suppF);
    Cudd_IterDerefBdd(dd,suppC); 
    return(NULL);
  }
  if (commonSupp == one) {
    Cudd_IterDerefBdd(dd,suppF);
    Cudd_IterDerefBdd(dd,suppC); 
    return(f);
  }
  cuddRef(commonSupp);
  Cudd_IterDerefBdd(dd,suppF);
  /* Abstract from c the variables that do not appear in f. */
  onlyC = Cudd_Cofactor(dd,suppC,commonSupp);
  if (onlyC == NULL) {
    Cudd_IterDerefBdd(dd,suppC); 
    Cudd_IterDerefBdd(dd,commonSupp); 
    return(NULL);
  }
  cuddRef(onlyC);
  Cudd_IterDerefBdd(dd,suppC); 
  Cudd_IterDerefBdd(dd,commonSupp); 
  cplus = Cudd_bddExistAbstract(dd, c, onlyC);
  if (cplus == NULL) {
    Cudd_IterDerefBdd(dd,onlyC); 
    return(NULL);
  }
  cuddRef(cplus);
  Cudd_IterDerefBdd(dd,onlyC);
  
  do {
    dd->reordered = 0;
    res = cuddauxAddRestrictRecur(dd, f, cplus);
  } while (dd->reordered == 1);
  if (res == NULL) {
    Cudd_IterDerefBdd(dd,cplus);
    return(NULL);
  }
  cuddRef(res);
  Cudd_IterDerefBdd(dd,cplus);
  cuddDeref(res);
  return(res);
} /* end of Cuddaux_addRestrict */



/**Function********************************************************************

  Synopsis    [Computes f constrain c for ADDs.]

  Description [Computes f constrain c (f @ c), for f an ADD and c a BDD.
  List of special cases:
    <ul>
    <li> F @ 0 = 0
    <li> F @ 1 = F
    <li> 0 @ c = 0
    <li> 1 @ c = 1
    </ul>
  Returns a pointer to the result if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     [Cudd_addConstrain]

******************************************************************************/
DdNode*
Cuddaux_addConstrain(DdManager * dd, DdNode * f, DdNode * c)
{
  DdNode *res;

  do {
    dd->reordered = 0;
    res = cuddauxAddConstrainRecur(dd,f,c);
  } while (dd->reordered == 1);
  return(res);
} /* end of Cuddaux_addConstrain */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cuddaux_addRestrict.]

  Description [Performs the recursive step of Cuddaux_addRestrict.
  Returns the restricted ADD if successful; otherwise NULL.]

  SideEffects [None]

  SeeAlso     [Cudd_addRestrict]

******************************************************************************/
DdNode *
cuddauxAddRestrictRecur(
  DdManager * dd,
  DdNode * f,
  DdNode * c)
{
  DdNode	 *Fv, *Fnv, *Cv, *Cnv, *t, *e, *res, *one, *zero;
  unsigned int topf, topc;
  int		 index;

  one = DD_ONE(dd);
  zero = Cudd_Not(one);

  /* Trivial cases */
  if (c == one)		return(f);
  if (c == zero){
    fprintf(stderr,"CuddauxAddRestrictRecur: warning: false careset\n");
    return(DD_BACKGROUND(dd));
  }
  if (Cudd_IsConstant(f)) return(f);

  /* Now f and c are non-constant. */

  /* Check the cache. */
  res = cuddCacheLookup2(dd, Cuddaux_addRestrict, f, c);
  if (res != NULL) {
    return(res);
  }

  topf = dd->perm[f->index];
  topc = dd->perm[Cudd_Regular(c)->index];

  if (topc < topf) {	/* abstract top variable from c */
    DdNode *d, *s1, *s2;

    /* Take the OR by applying DeMorgan. */
    /* Find complements of cofactors of c. */
    if (Cudd_IsComplement(c)) {
      s1 = cuddT(Cudd_Regular(c));
      s2 = cuddE(Cudd_Regular(c));
    } else {
      s1 = Cudd_Not(cuddT(c));
      s2 = Cudd_Not(cuddE(c));
    }
    /* Take the AND and negate */
    d = cuddBddAndRecur(dd, s1, s2);
    if (d == NULL) return(NULL);
    d = Cudd_Not(d);
    cuddRef(d);

    res = cuddauxAddRestrictRecur(dd, f, d);
    if (res == NULL) {
      Cudd_IterDerefBdd(dd, d);
      return(NULL);
    }
    cuddRef(res);
    Cudd_IterDerefBdd(dd, d);
    cuddDeref(res);
    cuddCacheInsert2(dd, Cuddaux_addRestrict, f, c, res);
    return(res);
  }

  /* Recursive step. Here topf <= topc. */
  index = f->index;
  Fv = cuddT(f); Fnv = cuddE(f);
  if (topc == topf) {
    Cv = Cudd_T(c); Cnv = Cudd_E(c);
    if (Cudd_IsComplement(c)) {
      Cv = Cudd_Not(Cv); Cnv = Cudd_Not(Cnv);
    }
  } else {
    Cv = Cnv = c;
  }

  if (!Cudd_IsConstant(Cv)) {
    t = cuddauxAddRestrictRecur(dd, Fv, Cv);
    if (t == NULL) return(NULL);
  } 
  else if (Cv == one) {
    t = Fv;
  } 
  else {		/* Cv == zero: return(Fnv @ Cnv) */
    if (Cnv == one) {
      res = Fnv;
    } 
    else {
      res = cuddauxAddRestrictRecur(dd, Fnv, Cnv);
      if (res == NULL) return(NULL);
    }
    return(res);
  }
  cuddRef(t);

  if (!Cudd_IsConstant(Cnv)) {
    e = cuddauxAddRestrictRecur(dd, Fnv, Cnv);
    if (e == NULL) {
      Cudd_RecursiveDeref(dd, t);
      return(NULL);
    }
  } else if (Cnv == one) {
    e = Fnv;
  } else {		/* Cnv == zero: return (Fv @ Cv) previously computed */
    cuddDeref(t);
    return(t);
  }
  cuddRef(e);

  res = (t == e) ? t : cuddUniqueInter(dd, index, t, e);
  if (res == NULL) {
    Cudd_RecursiveDeref(dd, e);
    Cudd_RecursiveDeref(dd, t);
    return(NULL);
  }
  cuddDeref(t);
  cuddDeref(e);

  cuddCacheInsert2(dd, Cuddaux_addRestrict, f, c, res);
  return(res);

} /* end of cuddauxAddRestrictRecur */

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cuddaux_addConstrain.]

  Description [Performs the recursive step of Cuddaux_addConstrain.
  Returns a pointer to the result if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     [Cuddaux_addConstrain]

******************************************************************************/
DdNode *
cuddauxAddConstrainRecur(
  DdManager * dd,
  DdNode * f,
  DdNode * c)
{
  DdNode       *Fv, *Fnv, *Cv, *Cnv, *t, *e, *res;
  DdNode	 *one, *zero;
  unsigned int topf, topc;
  int		 index;
  
  one = DD_ONE(dd);
  zero = Cudd_Not(one);
  
  /* Trivial cases. */
  if (c == one)		return(f);
  if (c == zero){
    fprintf(stderr,"CuddauxAddConstrainRecur: warning: false careset\n");
    return(DD_BACKGROUND(dd));
  }
  if (Cudd_IsConstant(f))	return(f);
  
  /* Now f and c are non-constant. */
  
  /* Check the cache. */
  res = cuddCacheLookup2(dd, Cuddaux_addConstrain, f, c);
  if (res != NULL) {
    return(res);
  }
  
  /* Recursive step. */
  topf = dd->perm[f->index];
  topc = dd->perm[Cudd_Regular(c)->index];
  if (topf <= topc) {
    index = f->index;
    Fv = cuddT(f); Fnv = cuddE(f);
  } else {
    index = Cudd_Regular(c)->index;
    Fv = Fnv = f;
  }
  if (topc <= topf) {
    Cv = Cudd_T(c); Cnv = Cudd_E(c);
    if (Cudd_IsComplement(c)) {
      Cv = Cudd_Not(Cv); Cnv = Cudd_Not(Cnv);
    }
  } else {
    Cv = Cnv = c;
  }
  
  if (!Cudd_IsConstant(Cv)) {
    t = cuddauxAddConstrainRecur(dd, Fv, Cv);
    if (t == NULL)
      return(NULL);
  } 
  else if (Cv == one) {
    t = Fv;
  } 
  else {		/* Cv == zero: return Fnv @ Cnv */
    if (Cnv == one) {
      res = Fnv;
    } 
    else {
      res = cuddauxAddConstrainRecur(dd, Fnv, Cnv);
      if (res == NULL)
	return(NULL);
    }
    return(res);
  }
  cuddRef(t);
  
  if (!Cudd_IsConstant(Cnv)) {
    e = cuddauxAddConstrainRecur(dd, Fnv, Cnv);
    if (e == NULL) {
      Cudd_RecursiveDeref(dd, t);
      return(NULL);
    }
  } 
  else if (Cnv == one) {
    e = Fnv;
  } 
  else {		/* Cnv == zero: return Fv @ Cv previously computed */
    cuddDeref(t);
    return(t);
  }
  cuddRef(e);
  
  res = (t == e) ? t : cuddUniqueInter(dd, index, t, e);
  if (res == NULL) {
    Cudd_RecursiveDeref(dd, e);
    Cudd_RecursiveDeref(dd, t);
    return(NULL);
  }
  cuddDeref(t);
  cuddDeref(e);
  
  cuddCacheInsert2(dd, Cuddaux_addConstrain, f, c, res);
  return(res);
  
} /* end of cuddauxAddConstrainRecur */
