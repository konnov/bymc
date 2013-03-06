/* $Id: cuddauxMisc.c,v 1.1.1.1 2002/05/14 13:04:04 bjeannet Exp $ */

/**CFile***********************************************************************

  FileName    [cuddauxMisc.c]

  PackageName [cuddaux]

  Synopsis    [Miscellaneous operations.]

  Description [Miscellaneous operations..]

	    External procedures included in this module:
		<ul>
		<li> Cuddaux_Support()
		<li> Cuddaux_SupportSize()
		<li> Cuddaux_ClassifySupport()
		<li> Cuddaux_IsVarIn()
		<li> Cuddaux_NodesBelowLevel()
		<li> cuddaux_list_free()
		<li> Cuddaux_addGuardOfNode()
		</ul>
	    Internal procedures included in this module:
		<ul>
		<li> cuddauxSupportRecur()
		<li> cuddauxIsVarInRecur()
		<li> cuddauxAddGuardOfNodeRecur()
		</ul>
	    Static procedures included in this module:
		<ul>
		<li> cuddauxNodesBelowLevelRecur()
		<li> cuddaux_list_add
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

static int cuddaux_list_add(cuddaux_list_t** const plist, DdNode* node);
static int cuddauxNodesBelowLevelRecur(DdManager* manager, DdNode* F, int level,
				       cuddaux_list_t** plist, st_table* visited,
				       size_t max, size_t *psize,
				       bool take_background);


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Finds the variables on which a DD depends.]

  Description [Finds the variables on which a DD depends.  Returns a BDD
  consisting of the product of the variables if successful; NULL otherwise.
  Variant of [Cudd_Support] using global cache.]

  SideEffects [None]

  SeeAlso     [Cudd_Support]

******************************************************************************/
DdNode* Cuddaux_Support(DdManager* dd, DdNode* f)
{
  DdNode* res;
  do {
    dd->reordered = 0;
    res = cuddauxSupportRecur(dd, Cudd_Regular(f));
  } while (dd->reordered == 1);
  return res;
}

/**Function********************************************************************

  Synopsis    [Finds the number of variables on which a DD depends, using Cuddaux_Support.]

  Description []

  SideEffects [None]

  SeeAlso     [Cudd_SupportSize]

******************************************************************************/
int Cuddaux_SupportSize(DdManager* dd, DdNode* f)
{
  DdNode* res;
  int size;
  res = Cuddaux_Support(dd,f);
  cuddRef(res);
  size = Cudd_DagSize(res) - 1;
  assert(size>=0);
  Cudd_IterDerefBdd(dd,res);
  return size;
}

/**Function********************************************************************

  Synopsis    [Classifies the variables in the support of two DDs.]

  Description [Classifies the variables in the support of two DDs
  <code>f</code> and <code>g</code>, depending on whther they appear
  in both DDs, only in <code>f</code>, or only in <code>g</code>.
  Returns 1 if successful; 0 otherwise.]

  SideEffects [The cubes of the three classes of variables are
  returned as side effects.]

  SeeAlso     []

******************************************************************************/
int
Cuddaux_ClassifySupport(
			DdManager * dd /* manager */,
			DdNode * f /* first DD */,
			DdNode * g /* second DD */,
			DdNode ** common /* cube of shared variables */,
			DdNode ** onlyF /* cube of variables only in f */,
			DdNode ** onlyG /* cube of variables only in g */)
{
  DdNode *suppF, *suppG;

  suppF = suppG = *common = *onlyF = *onlyG = NULL;

  suppF = Cuddaux_Support(dd,f);
  if (suppF == NULL) goto Cuddaux_ClassifySupport_error;
  cuddRef(suppF);

  suppG = Cuddaux_Support(dd,g);
  if (suppG == NULL) goto Cuddaux_ClassifySupport_error;
  cuddRef(suppG);

  *common = Cudd_bddLiteralSetIntersection(dd,suppF,suppG);
  if (*common == NULL) goto Cuddaux_ClassifySupport_error;
  cuddRef(*common);

  *onlyF = Cudd_Cofactor(dd,suppF,*common);
  if (*onlyF == NULL) goto Cuddaux_ClassifySupport_error;
  cuddRef(*onlyF);

  *onlyG = Cudd_Cofactor(dd,suppG,*common);
  if (*onlyG == NULL) goto Cuddaux_ClassifySupport_error;
  cuddRef(*onlyG);
  Cudd_IterDerefBdd(dd,suppF);
  Cudd_IterDerefBdd(dd,suppG);
  cuddDeref(*common);
  cuddDeref(*onlyF);
  cuddDeref(*onlyG);
  return 1;
 Cuddaux_ClassifySupport_error:
  if (suppF) Cudd_IterDerefBdd(dd,suppF);
  if (suppG) Cudd_IterDerefBdd(dd,suppG);
  if (*common){
    Cudd_IterDerefBdd(dd,*common);
    *common = NULL;
  }
  if (*onlyF){
    Cudd_IterDerefBdd(dd,*onlyF);
    *onlyF = NULL;
  }
  if (*onlyG){
    Cudd_IterDerefBdd(dd,*onlyG);
    *onlyG = NULL;
  }
  dd->errorCode = CUDD_MEMORY_OUT;
  return(0);
} /* end of Cuddaux_ClassifySupport */

/**Function********************************************************************

  Synopsis    [Membership of a variable to the support of a BDD/ADD]

  Description [Tells wether a variable appear in the decision diagram
  of a function.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
bool
Cuddaux_IsVarIn(DdManager* dd, DdNode* f, DdNode* var)
{
  assert(Cudd_Regular(var));
  return (cuddauxIsVarInRecur(dd,f,var) == DD_ONE(dd));
}

/* Given a \textsc{Bdd} or a \textsc{Add} $f$, and a variable level
  $l$, the function performs a depth-first search of the graph rooted
  at $f$ and select the first nodes encountered such that their
  variable level is equal or below the level $l$. If
  [[l==CUDD_MAXINDEX]], then the functions collects only constant
  nodes. */

/**Function********************************************************************

  Synopsis    [List of nodes below some level reachable from a root node.]

  Description [List of nodes below some level reachable from a root
  node. if max>0, the list is at most of size max (partial list).

  Given a BDD/ADD f and a variable level level the function
  performs a depth-first search of the graph rooted at $f$ and select
  the first nodes encountered such that their variable level is equal
  or below the level level. If level==CUDD_MAXINDEX, then the
  functions collects only constant nodes. The background node is not
  returned in the result if take_background==0.

  Returns the list of nodes, the index of which has its level equal or below
  level, and the size of the list in *psize, if successful; NULL
  otherwise. Nodes in the list are NOT referenced.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
cuddaux_list_t*
Cuddaux_NodesBelowLevel(DdManager* manager, DdNode* f, int level, size_t max, size_t* psize, bool take_background)
{
  cuddaux_list_t* res = 0;
  st_table* visited;

  visited = st_init_table(st_ptrcmp,st_ptrhash);
  if (visited==NULL) return NULL;
  *psize = 0;
  cuddauxNodesBelowLevelRecur(manager, Cudd_Regular(f), level, &res, visited, max, psize, take_background);
  if (res==NULL) *psize=0;
  assert (max>0 ? *psize<=max : 1);
  st_free_table(visited);
  return(res);
}

/**Function********************************************************************

  Synopsis    [Free a list returned by Cuddaux_NodesBelowLevel.]

  Description [Free a list returned by Cuddaux_NodesBelowLevel.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
void cuddaux_list_free(cuddaux_list_t* list)
{
  cuddaux_list_t* p;
  while (list!=0){
    p = list;
    list = list->next;
    free(p);
  }
}

/**Function********************************************************************

  Synopsis    [Logical guard of a node in an ADD.]

  Description [Logical guard of a node in an ADD.  h is supposed to be
  a ADD pointed from the ADD f. Returns a BDD which is the sum of the paths that
  leads from the root node f to the node h, if successful; NULL
  otherwise. ]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode* Cuddaux_addGuardOfNode(DdManager* manager, DdNode* f, DdNode* h)
{
  DdNode* res;
  do {
    manager->reordered = 0;
    res = cuddauxAddGuardOfNodeRecur(manager, f, h);
  } while (manager->reordered == 1);
  return res;
}

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cuddaux_Support.]

  Description [Performs the recursive step of Cuddaux_Support.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode*
cuddauxSupportRecur(DdManager* dd,
		    DdNode * f)
{
  DdNode *one, *fv, *fvn, *T,*E, *res, *res1;

  one = DD_ONE(dd);
  if (cuddIsConstant(f)) {
    return one;
  }
  fv = cuddT(f);
  fvn = Cudd_Regular(cuddE(f));
  if (cuddIsConstant(fv) && cuddIsConstant(fvn)){
    return dd->vars[f->index];
  }
  /* Look in the cache */
  res = cuddCacheLookup1(dd,Cuddaux_Support,f);
  if (res != NULL)
    return(res);

  T = cuddIsConstant(fv) ? one : cuddauxSupportRecur(dd,fv);
  if (T == NULL)
    return(NULL);
  cuddRef(T);
  E = cuddIsConstant(fvn) ? one : cuddauxSupportRecur(dd,fvn);
  if (E == NULL){
    Cudd_IterDerefBdd(dd,T);
    return(NULL);
  }
  if (T==E){
    res = cuddUniqueInter(dd,f->index,T,Cudd_Not(one));
    if (res == NULL){
      Cudd_IterDerefBdd(dd,T);
      return NULL;
    }
    cuddDeref(T);
  }
  else {
    cuddRef(E);
    res1 = cuddBddAndRecur(dd,T,E);
    if (res1 == NULL){
      Cudd_IterDerefBdd(dd,T);
      Cudd_IterDerefBdd(dd,E);
      return(NULL);
    }
    cuddRef(res1);
    Cudd_IterDerefBdd(dd,T);
    Cudd_IterDerefBdd(dd,E);
    res = cuddUniqueInter(dd,f->index,res1,Cudd_Not(one));
    if (res == NULL){
      Cudd_IterDerefBdd(dd,T);
      Cudd_IterDerefBdd(dd,E);
      Cudd_IterDerefBdd(dd,res1);
      return(NULL);
    }
    cuddDeref(res1);
  }
  cuddCacheInsert1(dd,Cuddaux_Support,f,res);
  return(res);
} /* end of cuddauxSupportRecur */


/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cuddaux_IsVarIn.]

  Description [Performs the recursive step of Cuddaux_IsVarIn. var is
  supposed to be a BDD projection function. Returns the logical one or
  zero.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode*
cuddauxIsVarInRecur(DdManager* manager, DdNode* f, DdNode* Var)
{
  DdNode *zero,*one, *F, *res;
  int topV,topF;

  one = DD_ONE(manager);
  zero = Cudd_Not(one);
  F = Cudd_Regular(f);

  if (cuddIsConstant(F)) return zero;
  if (Var==F) return(one);

  topV = Var->index;
  topF = F->index;
  if (topF == topV) return(one);
  if (cuddI(manager,topV) < cuddI(manager,topF)) return(zero);

  res = cuddCacheLookup2(manager,cuddauxIsVarInRecur, F, Var);
  if (res != NULL) return(res);
  res = cuddauxIsVarInRecur(manager,cuddT(F),Var);
  if (res==zero){
    res = cuddauxIsVarInRecur(manager,cuddE(F),Var);
  }
  cuddCacheInsert2(manager,cuddauxIsVarInRecur,F,Var,res);
  return(res);
}

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cuddaux_addGuardOfNode.]

  Description [Performs the recursive step of Cuddaux_addGuardOfNode.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/

DdNode*
cuddauxAddGuardOfNodeRecur(DdManager* manager, DdNode* f, DdNode* h)
{
  DdNode *one, *res, *T, *E;
  int topf, toph;

  /* Handle terminal cases */
  one = DD_ONE(manager);
  if (f==h){
    return(one);
  }
  topf = cuddI(manager,f->index);
  toph = cuddI(manager,h->index);
  if (topf >= toph){
    return Cudd_Not(one);
  }

  /* Look in the cache */
  res = cuddCacheLookup2(manager,Cuddaux_addGuardOfNode,f,h);
  if (res != NULL)
    return(res);

  T = cuddauxAddGuardOfNodeRecur(manager,cuddT(f),h);
  if (T == NULL)
    return(NULL);
  cuddRef(T);
  E = cuddauxAddGuardOfNodeRecur(manager,cuddE(f),h);
  if (E == NULL){
    Cudd_IterDerefBdd(manager, T);
    return(NULL);
  }
  cuddRef(E);
  if (T == E){
    res = T;
  }
  else {
    if (Cudd_IsComplement(T)){
      res = cuddUniqueInter(manager,f->index,Cudd_Not(T),Cudd_Not(E));
      if (res == NULL) {
	Cudd_IterDerefBdd(manager, T);
	Cudd_IterDerefBdd(manager, E);
	return(NULL);
      }
      res = Cudd_Not(res);
    }
    else {
      res = cuddUniqueInter(manager,f->index,T,E);
      if (res == NULL) {
	Cudd_IterDerefBdd(manager, T);
	Cudd_IterDerefBdd(manager, E);
	return(NULL);
      }
    }
  }
  cuddDeref(T);
  cuddDeref(E);
  cuddCacheInsert2(manager,Cuddaux_addGuardOfNode,f,h,res);
  return(res);
}

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cuddaux_NodesBelowLevelRecur.]

  Description [Performs the recursive step of
  Cuddaux_NodesBelowLevelRecur.  F is supposed to be a regular
  node. Returns 1 if successful, NULL otherwise.
  The background node is not put in the list if take_background==0 ]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static int
cuddauxNodesBelowLevelRecur(DdManager* manager, DdNode* F, int level,
			    cuddaux_list_t** plist, st_table* visited,
			    size_t max, size_t* psize,
			    bool take_background)
{
  int topF,res;

  if ((!take_background && F==DD_BACKGROUND(manager)) || st_is_member(visited, (char *) F) == 1){
    return 1;
  }
  topF = cuddI(manager,F->index);
  if (topF < level){
    res = cuddauxNodesBelowLevelRecur(manager, Cudd_Regular(cuddT(F)), level, plist, visited, max, psize, take_background);
    if (res==0) return 0;
    if (max == 0 || *psize<max){
      res = cuddauxNodesBelowLevelRecur(manager, Cudd_Regular(cuddE(F)), level, plist, visited, max, psize, take_background);
      if (res==0) return 0;
    }
  }
  else {
    res = cuddaux_list_add(plist,F);
    (*psize)++;
    if (res==0) return 0;
  }
  if (st_add_direct(visited, (char *) F, NULL) == ST_OUT_OF_MEM){
    cuddaux_list_free(*plist);
    return 0;
  }
  return 1;
}

/**Function********************************************************************

  Synopsis    [Add a node to a list of nodes.]

  Description [Add a node to a list of nodes. plist is the pointer to
  the list, and is an input/output parameter. Returns 1 if successful,
  0 otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static int
cuddaux_list_add(cuddaux_list_t** const plist, DdNode* node)
{
  cuddaux_list_t* nlist = (cuddaux_list_t*)malloc(sizeof(cuddaux_list_t));
  if (nlist==NULL) return(0);
  nlist->node = node;
  nlist->next = *plist;
  *plist = nlist;
  return 1;
}
