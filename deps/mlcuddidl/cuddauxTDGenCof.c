/* $Id: cuddauxTDGenCof.c,v 1.1.1.1 2002/05/14 13:04:04 bjeannet Exp $ */

/**CFile***********************************************************************

  FileName    [cuddauxTDGenCof.c]

  PackageName [cuddaux]

  Synopsis    [Top-Down generalized cofactors of Pascal Raymond.]

  Description [Top-Down generalized cofactors of Pascal Raymond.]

            External procedures included in this module:
		<ul>
		<li> Cuddaux_bddTDRestrict()
		<li> Cuddaux_bddTDConstrain()
		<li> Cuddaux_addTDRestrict()
		<li> Cuddaux_addTDConstrain()
		<li> Cuddaux_bddTDSimplify()
		<li> Cuddaux_addTDSimplify()
		</ul>
	    Internal procedures included in this module:
		<ul>
		<li> cuddauxBddTDSimplifyRecur()
		<li> cuddauxAddTDSimplifyRecur()
		<li> cuddauxAddTDUnify()
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

  Synopsis [BDD TDRestrict according to P. Raymond algorithm.]

  Description [BDD TDRestrict according to P. Raymond algorithm.
  f and c are BDDs.
  Returns the restricted BDD if successful; otherwise NULL.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/

DdNode* Cuddaux_bddTDRestrict(DdManager* dd, DdNode* f, DdNode* c)
{
  DdNode *suppF, *suppC, *commonSupp, *onlyC;
  DdNode *cplus, *res;
  DdNode *zero,*one;
  DdNode *inf,*sup;
  int retval;

  one = DD_ONE(dd);
  zero = Cudd_Not(one);
  if (c == one) return f;
  if (c == zero){
    fprintf(stderr,"Cuddaux_bddTDRestrict: warning: false careset\n");
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
  
  /* Computes the initial interval */
  inf = Cudd_bddAnd(dd,f,cplus); 
  if (inf == NULL){
    Cudd_IterDerefBdd(dd,cplus);
    return(NULL);
  }
  cuddRef(inf);
  sup = Cudd_bddOr(dd,f,Cudd_Not(cplus)); 
  if (sup == NULL){
    Cudd_IterDerefBdd(dd,cplus);
    Cudd_IterDerefBdd(dd,inf);
    return(NULL);
  }
  cuddRef(sup);
  Cudd_IterDerefBdd(dd,cplus);
  
  res = Cuddaux_bddTDSimplify(dd,inf,sup);
  cuddRef(res);
  Cudd_IterDerefBdd(dd,inf); 
  Cudd_IterDerefBdd(dd,sup);
  cuddDeref(res);
  return(res);
}

/**Function********************************************************************

  Synopsis [BDD TDConstrain according to P. Raymond algorithm.]

  Description [BDD TDRestrict according to P. Raymond algorithm.
  f and c are BDDs.
  Returns the restricted BDD if successful; otherwise NULL.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/

DdNode* Cuddaux_bddTDConstrain(DdManager* dd, DdNode* f, DdNode* c)
{
  DdNode *res;
  DdNode *zero,*one;
  DdNode *inf,*sup;

  one = DD_ONE(dd);
  zero = Cudd_Not(one);
  if (c == one) return f;
  if (c == zero){
    fprintf(stderr,"Cuddaux_bddTDConstrain: warning: false careset\n");
    return(zero);
  }
  if (Cudd_IsConstant(f)) return(f);
  if (f == c) return(one);
  if (f == Cudd_Not(c)) return(zero);

  inf = Cudd_bddAnd(dd,f,c); 
  if (inf == NULL) return(NULL);
  cuddRef(inf);
  sup = Cudd_bddOr(dd,f,Cudd_Not(c)); 
  if (sup == NULL){
    Cudd_IterDerefBdd(dd,inf);
    return(NULL);
  }
  cuddRef(sup);
  res = Cuddaux_bddTDSimplify(dd,inf,sup);
  cuddRef(res);
  Cudd_IterDerefBdd(dd,inf); 
  Cudd_IterDerefBdd(dd,sup);
  cuddDeref(res);
  return(res);
}


/**Function********************************************************************

  Synopsis [ADD TDRestrict according to P. Raymond algorithm.]

  Description [ADD TDRestrict according to P. Raymond algorithm.
  f is an ADD and c a BDDs.
  Suppose there is no background value in f.
  Returns the restricted ADD if successful; otherwise NULL.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode* Cuddaux_addTDRestrict(DdManager* dd, DdNode* f, DdNode* c)
{
  DdNode *suppF, *suppC, *commonSupp, *onlyC;
  DdNode *cplus, *phi, *res;
  DdNode *zero,*one;
  int retval;

  one = DD_ONE(dd);
  zero = Cudd_Not(one);
  if (c == one) return f;
  if (c == zero){
    fprintf(stderr,"Cuddaux_addTDRestrict: warning: false careset\n");
    return(NULL);
  }
  if (cuddIsConstant(f)) return f;
  
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
  
  /* Build the phi-ADD */
  phi = Cuddaux_addBddAnd(dd,cplus,f);
  if (phi == NULL){
    Cudd_IterDerefBdd(dd,cplus);
    return(NULL);
  }
  cuddRef(phi);
  Cudd_IterDerefBdd(dd,cplus);
  res = Cuddaux_addTDSimplify(dd,phi);
  cuddRef(res);
  Cudd_RecursiveDeref(dd,phi);
  cuddDeref(res);
  return(res);
}

/**Function********************************************************************

  Synopsis [ADD TDConstrain according to P. Raymond algorithm.]

  Description [ADD TDRestrict according to P. Raymond algorithm.
  f is an ADD and c a BDD.
  Suppose there is no background value in f.
  Returns the restricted ADD if successful; otherwise NULL.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode* 
Cuddaux_addTDConstrain(DdManager* dd, DdNode* f, DdNode* c)
{
  DdNode *zero,*one, *res;
  DdNode *phi;

  one = DD_ONE(dd);
  zero = Cudd_Not(one);
  if (c == one) return f;
  if (c == zero){
    fprintf(stderr,"Cuddaux_addTDFConstrain: warning: false careset\n");
    return(NULL);
  }
  if (cuddIsConstant(f)) return f;

  phi = Cuddaux_addBddAnd(dd,c,f);
  if (phi == NULL){
    return(NULL);
  }
  cuddRef(phi);
  res = Cuddaux_addTDSimplify(dd,phi);
  cuddRef(res);
  Cudd_RecursiveDeref(dd,phi);
  cuddDeref(res);
  return res;
}

/**Function********************************************************************

  Synopsis [BDD TDSimplify according to P. Raymond algorithm.]

  Description [BDD TDSimplify according to P. Raymond algorithm.
  inf and sup are BDDs.
  Returns a small BDD in the interval if successfull; otherwise NULL.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode*
Cuddaux_bddTDSimplify(DdManager * dd, DdNode * inf, DdNode * sup)
{
  DdNode *res;

  do {
    dd->reordered = 0;
    res = cuddauxBddTDSimplifyRecur(dd,inf,sup);
  } while (dd->reordered == 1);
  return(res);
} /* end of Cuddaux_bddTDSimplify */


/**Function********************************************************************

  Synopsis [ADD TDSimplify according to P. Raymond algorithm.]

  Description [ADD TDSimplify according to P. Raymond algorithm.
  f is a phi-ADD, i.e. an ADD with background values corresponding 
  to irrelevant paths.
  Returns an ADD without background if successfull; otherwise NULL.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode*
Cuddaux_addTDSimplify(DdManager * dd, DdNode * phi)
{
  DdNode *res;

  do {
    dd->reordered = 0;
    res = cuddauxAddTDSimplifyRecur(dd,phi);
  } while (dd->reordered == 1);
  return(res);
} /* end of Cuddaux_addTDSimplify */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cuddaux_bddTDSimplify.]

  Description [Performs the recursive step of Cuddaux_bddTDSimplify.]
  Returns a pointer to the result if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     [Cuddaux_bddTDSimplify]

******************************************************************************/
DdNode* 
cuddauxBddTDSimplifyRecur(DdManager* dd, DdNode* inf, DdNode* sup)
{
  DdNode *zero,*one;
  DdNode *ninf,*nsup,*Iv,*Inv,*Sv,*Snv,*res;
  int topI, topS, compl;
  
  one = DD_ONE(dd);
  zero = Cudd_Not(one);

  if (inf==zero) return inf;
  if (sup==one) return sup;

  /* Make canonical to increase the utilization of the cache. */
  compl=0;
  if (Cudd_IsComplement(sup)) {
    DdNode *t;
    t = Cudd_Not(sup);
    sup = Cudd_Not(inf);
    inf = t;
    compl = 1;
  }
  /* At this point sup is regular and non-constant; inf is
     non-constant, but may be complemented */
  res = cuddCacheLookup2(dd,Cuddaux_bddTDSimplify,inf,sup);
  if (res != NULL)
    return Cudd_NotCond(res,compl);

  topI = cuddI(dd,Cudd_Regular(inf)->index);
  topS = cuddI(dd,sup->index);
  if (topS < topI){
    /* Compute the AND of cofactors of sup */
    Sv = cuddT(sup);
    Snv = cuddE(sup);
    nsup = cuddBddAndRecur(dd,Sv,Snv);
    if (nsup == NULL) return NULL;
    cuddRef(nsup);
    res = cuddauxBddTDSimplifyRecur(dd,inf,nsup);
    if (res == NULL){
      Cudd_IterDerefBdd(dd,nsup);
      return(NULL);
    }
    cuddRef(res);
    Cudd_IterDerefBdd(dd,nsup);
  }
  else if (topI < topS){
    /* Compute the OR of cofactors of inf (= NAND of their negation) */
    Iv = Cudd_T(inf);
    Inv = Cudd_E(inf);
    if (!Cudd_IsComplement(inf)){
      Iv = Cudd_Not(Iv);
      Inv = Cudd_Not(Inv);
    }
    ninf = cuddBddAndRecur(dd,Iv,Inv);
    if (ninf == NULL) return(NULL);
    ninf = Cudd_Not(ninf);
    cuddRef(ninf);
    res = cuddauxBddTDSimplifyRecur(dd,ninf,sup);
    if (res == NULL){
      Cudd_IterDerefBdd(dd,ninf);
      return(NULL);
    }
    cuddRef(res);
    Cudd_IterDerefBdd(dd,ninf);
  }
  else {
    /* Try the best */
    Iv = Cudd_T(inf);
    Inv = Cudd_E(inf);
    if (Cudd_IsComplement(inf)){
      Iv = Cudd_Not(Iv);
      Inv = Cudd_Not(Inv);
    }
    Sv = cuddT(sup);
    Snv = cuddE(sup);
    if (Cudd_bddLeq(dd,Iv,Snv) && Cudd_bddLeq(dd,Inv,Sv)){
      /* Compute the AND of cofactors of sup */
      nsup = cuddBddAndRecur(dd,Sv,Snv);
      if (nsup == NULL) return NULL;
      cuddRef(nsup);
      /* Compute the OR of cofactors of inf (= NAND of their negation) */
      Iv = Cudd_Not(Iv);
      Inv = Cudd_Not(Inv);
      ninf = cuddBddAndRecur(dd,Iv,Inv);
      if (ninf == NULL){
	Cudd_IterDerefBdd(dd,nsup);
	return(NULL);
      }
      ninf = Cudd_Not(ninf);
      cuddRef(ninf);
      res = cuddauxBddTDSimplifyRecur(dd,ninf,nsup);
      if (res == NULL){
	Cudd_IterDerefBdd(dd,ninf);
	Cudd_IterDerefBdd(dd,nsup);
	return(NULL);
      }
      cuddRef(res);
      Cudd_IterDerefBdd(dd,ninf);
      Cudd_IterDerefBdd(dd,nsup);
    }
    else {
      ninf = cuddauxBddTDSimplifyRecur(dd,Iv,Sv);
      if (ninf == NULL) return(NULL);
      cuddRef(ninf);
      nsup = cuddauxBddTDSimplifyRecur(dd,Inv,Snv);
      if (nsup == NULL){
	Cudd_IterDerefBdd(dd,ninf);
	return(NULL);
      }
      cuddRef(nsup);
      if (Cudd_IsComplement(ninf)) {
	ninf = Cudd_Not(ninf);
	nsup = Cudd_Not(nsup);
	res = (ninf==nsup) ? ninf : cuddUniqueInter(dd,sup->index,ninf,nsup);
	if (res == NULL){
	  Cudd_IterDerefBdd(dd,ninf);
	  Cudd_IterDerefBdd(dd,nsup);
	  return(NULL);
	}
	res = Cudd_Not(res);
      } else {
	res = (ninf==nsup) ? ninf : cuddUniqueInter(dd,sup->index,ninf,nsup);
	if (res == NULL){
	  Cudd_IterDerefBdd(dd,ninf);
	  Cudd_IterDerefBdd(dd,nsup);
	  return(NULL);
	}
      }
      cuddRef(res);
      cuddDeref(ninf);
      cuddDeref(nsup);
    }
  }
  cuddDeref(res);
  cuddCacheInsert2(dd,Cuddaux_bddTDSimplify,inf,sup,res);
  return Cudd_NotCond(res,compl);
}

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cuddaux_addTDSimplify.]

  Description [Performs the recursive step of Cuddaux_addTDSimplify.]
  Returns a pointer to the result if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     [Cuddaux_addTDSimplify]

******************************************************************************/
DdNode*
cuddauxAddTDSimplifyRecur(DdManager* dd, DdNode* f)
{
  DdNode *res;
  DdNode *U,*T,*E;
  
  if (cuddIsConstant(f))
    return f;

  res = cuddCacheLookup1(dd,Cuddaux_addTDSimplify,f);
  if (res != NULL) 
    return res;
  
  U = cuddauxAddTDUnify(dd,cuddT(f),cuddE(f));
  if (U == NULL)
    return(NULL);
  else if (U == (DdNode*)1){
    T = cuddauxAddTDSimplifyRecur(dd,cuddT(f));
    if (T == NULL) return(NULL);
    cuddRef(T);
    E = cuddauxAddTDSimplifyRecur(dd,cuddE(f));
    if (E == NULL){
      Cudd_RecursiveDeref(dd,T);
      return(NULL);
    }
    cuddRef(E);
    res = (T==E) ? T : cuddUniqueInter(dd,f->index,T,E);
    if (res == NULL){
      Cudd_RecursiveDeref(dd,T);
      Cudd_RecursiveDeref(dd,E);
      return(NULL);
    }
    cuddDeref(T);
    cuddDeref(E);
  }
  else {
    cuddRef(U);
    res = cuddauxAddTDSimplifyRecur(dd,U);
    if (res == NULL){
      Cudd_RecursiveDeref(dd,U);
      return(NULL);
    }
    cuddRef(res);
    Cudd_RecursiveDeref(dd,U);
    cuddDeref(res);
  }
  cuddCacheInsert1(dd,Cuddaux_addTDSimplify,f,res);
  return res;
}

DdNode* 
cuddauxAddTDUnify(DdManager* dd, DdNode* f, DdNode* g)
{
  DdNode *fv,*fnv,*gv,*gnv,*res;
  DdNode *T,*E;
  int topf,topg,index;
  
  if (f==g) return f;
  if (f==DD_BACKGROUND(dd)) return g;
  if (g==DD_BACKGROUND(dd)) return f;
  if (cuddIsConstant(f) && cuddIsConstant(g) && cuddV(f)!=cuddV(g))
    return((DdNode*)1);
  if (f>g){
    DdNode* t=f; f=g; g=t;
  }
  res = cuddCacheLookup2(dd,cuddauxAddTDUnify,f,g);
  if (res != NULL) 
    return res;

  topf = cuddI(dd,f->index);
  topg = cuddI(dd,g->index);
  if (topf <= topg){
    index = f->index;
    fv = cuddT(f); fnv = cuddE(f);
  }
  else {
    index = g->index;
    fv = fnv = f;
  }
  if (topg <= topf){
    gv = cuddT(g); gnv = cuddE(g);
  }
  else {
    gv = gnv = g;
  }

  T = cuddauxAddTDUnify(dd,fv,gv);
  if (T==NULL || T==(DdNode*)1){
    return T;
  }
  cuddRef(T);
  E = cuddauxAddTDUnify(dd,fnv,gnv);
  if (E==NULL || E==(DdNode*)1){
    Cudd_RecursiveDeref(dd,T);
    return E;
  }
  cuddRef(E);
  res = (T==E) ? T : cuddUniqueInter(dd,index,T,E);
  cuddDeref(T);
  cuddDeref(E);
  cuddCacheInsert2(dd,cuddauxAddTDUnify,f,g,res);
  return res;
}

