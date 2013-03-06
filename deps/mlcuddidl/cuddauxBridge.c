/* $Id: cuddauxBridge.c,v 1.2 2005/06/14 14:37:56 bjeannet Exp $ */

/**CFile***********************************************************************

  FileName    [cuddauxBridge.c]

  PackageName [cuddaux]

  Synopsis    [Transfer between different managers.]

  Description [External procedures included in this file:
	    <ul>
	    <li> Cuddaux_addTransfer()
	    <li> Cuddaux_addCamlTransfer()
	    </ul>
	Internal procedures included in this file:
	    <ul>
	    <li> cuddauxAddTransfer()
	    <li> cuddauxAddCamlTransfer()
	    </ul>
	Static procedures included in this file:
	    <ul>
	    <li> cuddauxAddTransferRecur()
	    <li> cuddauxAddCamlTransferRecur()
	    </ul>
	    ]

  SeeAlso     []

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

static DdNode* cuddauxAddTransferRecur(DdManager *ddS, DdManager *ddD, 
				       DdNode *f, st_table *table);

static DdNode* cuddauxAddCamlTransferRecur(DdManager *ddS, DdManager *ddD, 
					   DdNode *f, st_table *table);

/**AutomaticEnd***************************************************************/

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Convert a ADD from a manager to another one.]

  Description [Convert a ADD from a manager to another one. The orders of the
  variables in the two managers may be different. Returns a
  pointer to the ADD in the destination manager if successful; NULL
  otherwise.]

  SideEffects [None]

  SeeAlso     [Cudd_bddTransfer]

******************************************************************************/
DdNode*
Cuddaux_addTransfer(
  DdManager * ddSource,
  DdManager * ddDestination,
  DdNode * f)
{
    DdNode *res;
    do {
	ddDestination->reordered = 0;
	res = cuddauxAddTransfer(ddSource, ddDestination, f);
    } while (ddDestination->reordered == 1);
    return(res);

} /* end of Cuddaux_addTransfer */

DdNode*
Cuddaux_addCamlTransfer(
  DdManager * ddSource,
  DdManager * ddDestination,
  DdNode * f)
{
    DdNode *res;
    do {
      ddDestination->reordered = 0;
      res = cuddauxAddCamlTransfer(ddSource, ddDestination, f);
    } while (ddDestination->reordered == 1);
    return(res);
} 

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Convert a BDD from a manager to another one.]

  Description [Convert a BDD from a manager to another one. Returns a
  pointer to the BDD in the destination manager if successful; NULL
  otherwise.]

  SideEffects [None]

  SeeAlso     [Cuddaux_addTransfer]

******************************************************************************/
DdNode*
cuddauxAddTransfer(
  DdManager * ddS,
  DdManager * ddD,
  DdNode* f)
{
    DdNode *res;
    st_table *table = NULL;
    st_generator *gen = NULL;
    DdNode *key, *value;

    table = st_init_table(st_ptrcmp,st_ptrhash);
    if (table == NULL) goto failure;
    res = cuddauxAddTransferRecur(ddS, ddD, f, table);
    if (res != NULL) cuddRef(res);

    /* Dereference all elements in the table and dispose of the table.
    ** This must be done also if res is NULL to avoid leaks in case of
    ** reordering. */
    gen = st_init_gen(table);
    if (gen == NULL) goto failure;
    while (st_gen(gen, &key, &value)) {
	Cudd_RecursiveDeref(ddD, value);
    }
    st_free_gen(gen); gen = NULL;
    st_free_table(table); table = NULL;

    if (res != NULL) cuddDeref(res);
    return(res);

failure:
    if (table != NULL) st_free_table(table);
    if (gen != NULL) st_free_gen(gen);
    return(NULL);

} /* end of cuddauxAddTransfer */

DdNode*
cuddauxAddCamlTransfer(
  DdManager * ddS,
  DdManager * ddD,
  DdNode* f)
{
    DdNode *res;
    st_table *table = NULL;
    st_generator *gen = NULL;
    DdNode *key, *value;

    table = st_init_table(st_ptrcmp,st_ptrhash);
    if (table == NULL) goto failure;
    res = cuddauxAddCamlTransferRecur(ddS, ddD, f, table);
    if (res != NULL) cuddRef(res);

    /* Dereference all elements in the table and dispose of the table.
    ** This must be done also if res is NULL to avoid leaks in case of
    ** reordering. */
    gen = st_init_gen(table);
    if (gen == NULL) goto failure;
    while (st_gen(gen, &key, &value)) {
	Cudd_RecursiveDeref(ddD, value);
    }
    st_free_gen(gen); gen = NULL;
    st_free_table(table); table = NULL;

    if (res != NULL) cuddDeref(res);
    return(res);

failure:
    if (table != NULL) st_free_table(table);
    if (gen != NULL) st_free_gen(gen);
    return(NULL);

}
/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cudd_bddTransfer.]

  Description [Performs the recursive step of Cudd_bddTransfer.
  Returns a pointer to the result if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     [cuddauxAddTransfer]

******************************************************************************/
static DdNode *
cuddauxAddTransferRecur(
  DdManager * ddS,
  DdManager * ddD,
  DdNode * f,
  st_table * table)
{
  DdNode *ft, *fe, *t, *e, *var, *res;
  DdNode *one, *zero;
  int	   index;

  /* Trivial cases. */
  if (cuddIsConstant(f)){
    double v = cuddV(f);
    return (cuddUniqueConst(ddD,v));
  }
  /* Check the cache. */
  if(st_lookup(table, f, &res))
    return(res);
    
  /* Recursive step. */
  index = f->index;
  ft = cuddT(f); fe = cuddE(f);

  t = cuddauxAddTransferRecur(ddS, ddD, ft, table);
  if (t == NULL) {
    return(NULL);
  }
  cuddRef(t);

  e = cuddauxAddTransferRecur(ddS, ddD, fe, table);
  if (e == NULL) {
    Cudd_RecursiveDeref(ddD, t);
    return(NULL);
  }
  cuddRef(e);

  one = DD_ONE(ddD);
  zero = Cudd_Not(one);
  var = cuddUniqueInter(ddD,index,one,zero);
  if (var == NULL) {
    Cudd_RecursiveDeref(ddD, t);
    Cudd_RecursiveDeref(ddD, e);
    return(NULL);
  }
  res = cuddauxAddIteRecur(ddD,var,t,e);
  if (res == NULL) {
    Cudd_RecursiveDeref(ddD, t);
    Cudd_RecursiveDeref(ddD, e);
    return(NULL);
  }
  cuddRef(res);
  Cudd_RecursiveDeref(ddD, t);
  Cudd_RecursiveDeref(ddD, e);

  if (st_add_direct(table, (char *) f, (char *) res) == ST_OUT_OF_MEM) {
    Cudd_RecursiveDeref(ddD, res);
    return(NULL);
  }
  return(res);

} /* end of cuddauxAddTransferRecur */

static DdNode *
cuddauxAddCamlTransferRecur(
  DdManager * ddS,
  DdManager * ddD,
  DdNode * f,
  st_table * table)
{
  DdNode *ft, *fe, *t, *e, *var, *res;
  DdNode *one, *zero;
  int	   index;

  /* Trivial cases. */
  if (cuddIsConstant(f)){
    value value = f->type.value;
    return (Cuddaux_addCamlConst(ddD,value));
  }
  /* Check the cache. */
  if(st_lookup(table, f, &res))
    return(res);
    
  /* Recursive step. */
  index = f->index;
  ft = cuddT(f); fe = cuddE(f);

  t = cuddauxAddCamlTransferRecur(ddS, ddD, ft, table);
  if (t == NULL) {
    return(NULL);
  }
  cuddRef(t);

  e = cuddauxAddCamlTransferRecur(ddS, ddD, fe, table);
  if (e == NULL) {
    Cudd_RecursiveDeref(ddD, t);
    return(NULL);
  }
  cuddRef(e);

  one = DD_ONE(ddD);
  zero = Cudd_Not(one);
  var = cuddUniqueInter(ddD,index,one,zero);
  if (var == NULL) {
    Cudd_RecursiveDeref(ddD, t);
    Cudd_RecursiveDeref(ddD, e);
    return(NULL);
  }
  res = cuddauxAddIteRecur(ddD,var,t,e);
  if (res == NULL) {
    Cudd_RecursiveDeref(ddD, t);
    Cudd_RecursiveDeref(ddD, e);
    return(NULL);
  }
  cuddRef(res);
  Cudd_RecursiveDeref(ddD, t);
  Cudd_RecursiveDeref(ddD, e);

  if (st_add_direct(table, (char *) f, (char *) res) == ST_OUT_OF_MEM) {
    Cudd_RecursiveDeref(ddD, res);
    return(NULL);
  }
  return(res);

}
