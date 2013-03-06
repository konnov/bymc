/* $Id: cuddaux.h,v 1.1.1.1 2002/05/14 13:04:04 bjeannet Exp $ */

#ifndef __CUDDAUX_H__
#define __CUDDAUX_H__

#include <stdbool.h>
#include <stdint.h>
#include <assert.h>
#include "cudd.h"
#include "cuddInt.h"
#include "caml/mlvalues.h"
#include "caml/alloc.h"

extern value camlidl_cudd_custom_op_exn;

/* ********************************************************************** */
/* Types */
/* ********************************************************************** */

typedef union CuddauxType {
  CUDD_VALUE_TYPE dbl;	/* for constant nodes */
  value value;          /* for constant nodes */
  DdChildren kids;	/* for internal nodes */
} CuddauxType;
typedef struct CuddauxDdNode {
  DdHalfWord index;
  DdHalfWord ref;	/* reference count */
  DdNode *next;		/* next pointer for unique table */
  CuddauxType type;
} CuddauxDdNode;

struct CuddauxMan {
  DdManager* man;
  size_t count;
  bool caml; /* true: support Caml values in ADD leaves, false: does not */
};

struct CuddauxHash {
  DdHashTable* hash;
  size_t arity;
  size_t initialsize;
  struct CuddauxMan* man;
};

struct node__t {
  struct CuddauxMan* man;
  DdNode* node;
};

struct CuddauxCache {
  DdLocalCache* cache;
  size_t arity;
  size_t initialsize;
  size_t maxsize;
  struct CuddauxMan* man;
};
typedef struct CuddauxCache* CuddauxCache;

typedef void* pid;
enum memo_discr { Global, Cache, Hash };
union memo_union {
  struct CuddauxCache* cache;
  struct CuddauxHash* hash;
};
struct memo__t {
  enum memo_discr discr;
  union memo_union u;
};
struct common {
  pid pid;
  int arity;
  struct memo__t memo;
  struct CuddauxMan* man;
  value exn;
};
struct op1 {
  struct common common1;
  value closure1;
  DdNode* (*funptr1)(DdManager*, struct op1*,DdNode*);
};
struct op2 {
  struct common common2;
  value closure2;
  value ospecial2;
  bool commutative;
  bool idempotent;
  DdNode* (*funptr2)(DdManager*, struct op2*,DdNode*,DdNode*);
};
struct test2 {
  struct common common2t;
  value closure2t;
  value ospecial2t;
  bool symetric;
  bool reflexive;
  DdNode* (*funptr2t)(DdManager*, struct test2*,DdNode*,DdNode*);
};
struct op3 {
  struct common common3;
  value closure3;
  value ospecial3;
  DdNode* (*funptr3)(DdManager*, struct op3*,DdNode*,DdNode*,DdNode*);
};
struct opN {
  struct common commonN;
  int arityNbdd;
  value closureN;
  DdNode* (*funptrN)(DdManager*, struct opN*, DdNode**);
};
struct opG {
  struct common commonG;
  int arityGbdd;
  value closureG;
  DdNode* (*funptrG)(DdManager*, struct opG*,DdNode**);
  value oclosureBeforeRec;
  DdNode* (*funptrBeforeRec)(DdManager*, struct opG*, DdNode*, DdNode**);
  value oclosureIte;
  DdNode* (*funptrIte)(DdManager*, struct opG*, int, DdNode*, DdNode*);
};
struct exist {
  struct common commonexist;
  struct op2 combineexist;
};
struct existand {
  struct common commonexistand;
  struct op2 combineexistand;
  value bottomexistand;
};
struct existop1 {
  struct common commonexistop1;
  struct op2 combineexistop1;
  struct op1 existop1;
};
struct existandop1 {
  struct common commonexistandop1;
  struct op2 combineexistandop1;
  struct op1 existandop1;
  value bottomexistandop1;
};

struct cuddaux_list_t {
  struct cuddaux_list_t* next;
  DdNode* node;
};
typedef struct cuddaux_list_t cuddaux_list_t;

/* ********************************************************************** */
/* Function Prototypes */
/* ********************************************************************** */

void cuddauxManFree(struct CuddauxMan* man);
DdLocalCache* cuddauxCacheReinit(struct CuddauxMan* man, struct CuddauxCache* cache);
DdHashTable* cuddauxHashReinit(struct CuddauxMan* man, struct CuddauxHash* hash);
DdNode* cuddauxCommonLookupN(struct common* common, DdNode** tab);
DdNode* cuddauxCommonInsertN(struct common* common, DdNode** tab, DdNode* res);

/* f is a BDD, g and h are ADDs */
DdNode* Cuddaux_addIte(DdManager* dd, DdNode* f, DdNode* g, DdNode* h);
DdNode* Cuddaux_addBddAnd(DdManager* dd, DdNode* f, DdNode* g);
DdNode* Cuddaux_addIteConstant(DdManager* dd, DdNode* f, DdNode* g, DdNode* h);
DdNode* Cuddaux_addEvalConst(DdManager* dd, DdNode* f, DdNode* g);

/* f is an ADD */
DdNode* Cuddaux_addTransfer(DdManager* ddS, DdManager* ddD, DdNode* f);

/* f and c are BDDs */
DdNode* Cuddaux_bddRestrict(DdManager * dd, DdNode * f, DdNode * c);
/* f is an ADD, c a BDD */
DdNode* Cuddaux_addRestrict(DdManager * dd, DdNode * f, DdNode * c);
DdNode* Cuddaux_addConstrain(DdManager * dd, DdNode * f, DdNode * c);

/* f and c are BDDs */
DdNode* Cuddaux_bddTDRestrict(DdManager* dd, DdNode* f, DdNode* c);
DdNode* Cuddaux_bddTDConstrain(DdManager* dd, DdNode* f, DdNode* c);
/* f is an ADD, c a BDD */
DdNode* Cuddaux_addTDRestrict(DdManager* dd, DdNode* f, DdNode* c);
DdNode* Cuddaux_addTDConstrain(DdManager* dd, DdNode* f, DdNode* c);
/* inf and sup are BDDs */
DdNode* Cuddaux_bddTDSimplify(DdManager* dd, DdNode* inf, DdNode* sup);
/* phi,f,g are ADDs with the distinguished background value */
DdNode* Cuddaux_addTDSimplify(DdManager* dd, DdNode* phi);

/* f is an ADD, g a BDD */
DdNode* Cuddaux_addCompose(DdManager* dd, DdNode* f, DdNode* g, int v);
DdNode* Cuddaux_addVarMap(DdManager* dd, DdNode* f);
int Cuddaux_SetVarMap(DdManager *manager, int* array, int size);
/* f is an ADD, vector an array of BDDs */
DdNode* Cuddaux_addVectorComposeCommon(struct common* common,
				       DdNode* f, DdNode** vector);
DdNode* Cuddaux_addPermuteCommon(struct common* common, DdNode* f, int* permut);
DdNode* Cuddaux_addVectorCompose(struct CuddauxMan* man, DdNode* f, DdNode** vector);
/* f is a BDD, vector an array of BDDs */
DdNode* Cuddaux_bddVectorComposeCommon(struct common* common, DdNode* f, DdNode** vector);
DdNode* Cuddaux_bddPermuteCommon(struct common* common, DdNode* f, int* permut);

/* f, g and h are ADDs */
DdNode* Cuddaux_addApply1(struct op1* op, DdNode* f);
DdNode* Cuddaux_addApply2(struct op2* op, DdNode* f, DdNode* g);
int Cuddaux_addTest2(struct test2* op, DdNode* f, DdNode* g);
DdNode* Cuddaux_addApply3(struct op3* op, DdNode* f, DdNode* g, DdNode* h);
DdNode* Cuddaux_addApplyN(struct opN* op, DdNode** tab);
DdNode* Cuddaux_addApplyG(struct opG* op, DdNode** tab);
DdNode* Cuddaux_addAbstract(struct exist* op, DdNode* f, DdNode* cube);
DdNode* Cuddaux_addApplyAbstract(struct existop1* op, DdNode* f, DdNode* cube);
DdNode*
Cuddaux_addBddAndAbstract(struct existand* op,
			  DdNode* f, DdNode* G,
			  DdNode* cube, DdNode* background);
DdNode*
Cuddaux_addApplyBddAndAbstract(struct existandop1* op,
			       DdNode* f, DdNode* G,
			       DdNode* cube, DdNode* background);

/* f is a BDD/ADD node */
DdNode* Cuddaux_Support(DdManager* dd, DdNode* f);
int Cuddaux_SupportSize(DdManager* dd, DdNode* f);
int Cuddaux_ClassifySupport(DdManager* dd, DdNode* f, DdNode* g, DdNode** common, DdNode** onlyF, DdNode** onlyG);
/* f is a BDD/ADD node and var a projection function */
bool Cuddaux_IsVarIn(DdManager* dd, DdNode* f, DdNode* var);
/* f is a BDD/ADD node and level a level. */
cuddaux_list_t* Cuddaux_NodesBelowLevel(DdManager* dd, DdNode* f, int level, size_t max, size_t* psize, bool take_background);
void cuddaux_list_free(cuddaux_list_t* l);
/* f and h are ADDs */
DdNode* Cuddaux_addGuardOfNode(DdManager* dd, DdNode* f, DdNode* h);
DdNode* Cuddaux_addCamlConst(DdManager* unique, value value);
int Cuddaux_addCamlPreGC(DdManager* unique, const char* s, void* data);


/* f is a BDD, g and h are ADDs */
DdNode* cuddauxAddIteRecur(DdManager* dd, DdNode* f, DdNode* g, DdNode* h);
DdNode* cuddauxAddBddAndRecur(DdManager* dd, DdNode* f, DdNode* g);
/* f is an ADD */
DdNode* cuddauxAddTransfer(DdManager* ddS, DdManager* ddD, DdNode* f);
DdNode* cuddauxAddCamlTransfer(DdManager* ddS, DdManager* ddD, DdNode* f);
DdNode* cuddauxAddRestrictRecur(DdManager * dd, DdNode * f, DdNode * c);
DdNode* cuddauxAddConstrainRecur(DdManager * dd, DdNode * f, DdNode * c);
/* inf and sup are BDDs */
DdNode* cuddauxBddTDSimplifyRecur(DdManager* dd, DdNode* inf, DdNode* sup);
/* phi,f,g are ADDs with the distinguished background value */
DdNode* cuddauxAddTDSimplifyRecur(DdManager* dd, DdNode* phi);
DdNode* cuddauxAddTDUnify(DdManager* dd, DdNode* f, DdNode* g);
/* f is an ADD, vector an array of BDDs */
DdNode* cuddauxAddVarMapRecur(DdManager *manager, DdNode* f);
DdNode* cuddauxAddComposeRecur(DdManager* dd, DdNode* f, DdNode* g, DdNode* proj);
DdNode* cuddauxAddVectorComposeRecur(
  struct common* common,
  DdNode * f /* ADD in which to compose */,
  DdNode ** vector /* functions to substitute */,
  int  deepest /* depth of deepest substitution */);
DdNode* cuddauxBddVectorComposeRecur(
  struct common* common,
  DdNode * f /* BDD in which to compose */,
  DdNode ** vector /* functions to substitute */,
  int  deepest /* depth of deepest substitution */);
/* f, g and h are ADDs */
DdNode* cuddauxAddApply1Recur(DdManager* dd, struct op1* op, DdNode* f);
DdNode* cuddauxAddApply2Recur(DdManager* dd, struct op2* op, DdNode* f, DdNode* g);
DdNode* cuddauxAddTest2Recur(DdManager* dd, struct test2* op, DdNode* f, DdNode* g);
DdNode* cuddauxAddApply3Recur(DdManager* dd, struct op3* op, DdNode* f, DdNode* g, DdNode* h);
DdNode* cuddauxAddApplyNRecur(DdManager * dd, struct opN* op, DdNode ** tab);
DdNode* cuddauxAddApplyGRecur(DdManager * dd, struct opG* op, DdNode ** tab);
DdNode* cuddauxAddAbstractRecur(DdManager * dd,
			struct exist* op,
			DdNode * f, /* ADD */
			DdNode * cube /* BDD (cube) */);
DdNode*
cuddauxAddApplyAbstractRecur(DdManager * dd,
			     struct existop1* op,
			     DdNode * f, /* ADD */
			     DdNode * cube /* BDD (cube) */);
DdNode*
cuddauxAddBddAndAbstractRecur(DdManager * dd,
			      struct existand* op,
			      DdNode * f, /* BDD */
			      DdNode * G, /* ADD */
			      DdNode * cube, /* BDD (cube) */
			      DdNode * background /* CST ADD */);
DdNode*
cuddauxAddApplyBddAndAbstractRecur(DdManager * dd,
				   struct existandop1* op,
				   DdNode * f, /* BDD */
				   DdNode * G, /* ADD */
				   DdNode * cube, /* BDD (cube) */
				   DdNode * background /* CST ADD */);
/* f is a BDD/ADD node */
DdNode* cuddauxSupportRecur(DdManager* dd, DdNode* f);
/* f is a BDD/ADD node and index the index of a variable.*/
DdNode* cuddauxIsVarInRecur(DdManager* manager, DdNode* Var, DdNode* f);
/* f and h are ADDs */
DdNode* cuddauxAddGuardOfNodeRecur(DdManager* manager, DdNode* f, DdNode* h);

void cuddauxAddCamlConstRehash(DdManager* unique, int offset);

/* Cache tags for 3-operand operators.
   Look at cuddInt.h for already used tags.
   Begins from the end */

#define DDAUX_ADD_ITE_TAG            0xee
#define DDAUX_ADD_ITE_CONSTANT_TAG   0xea
#define DDAUX_ADD_COMPOSE_RECUR_TAG  0xe6

/* ********************************************************************** */
/* Inline Functions */
/* ********************************************************************** */
#define DD_BACKGROUND(dd)		((dd)->background)
#define cuddauxCamlV(_node_) (((CuddauxDdNode*)_node_)->type.value)
static inline DdNode* cuddauxUniqueType(struct CuddauxMan* man, CuddauxType* type)
{
  return man->caml ?
    Cuddaux_addCamlConst(man->man,type->value) :
    cuddUniqueConst(man->man,type->dbl);
}
static inline value Val_type(bool caml, CuddauxType* type)
{
  return caml ? type->value : copy_double(type->dbl);
}
static inline value Val_DdNode(bool caml, DdNode* node)
{
  CuddauxType type = ((CuddauxDdNode*)node)->type;
  return Val_type(caml,&type);
}
static inline CuddauxType Type_val(bool caml, value val)
{
  CuddauxType type;
  if (caml)
    type.value = val;
  else
    type.dbl = Double_val(val);
  return type;
}
static inline CuddauxType CuddauxType_DdNode(DdNode* node)
{
  return ((CuddauxDdNode*)node)->type;
}
static inline bool CuddauxTypeEqual(bool caml, CuddauxType* type1, CuddauxType* type2)
{
  return caml ? type1->value==type2->value : type1->dbl == type2->dbl;
}

#define cuddauxManRef(x) do { if((x)->count<SIZE_MAX) (x)->count++; } while(0)
static inline struct CuddauxMan* cuddauxManCopy(struct CuddauxMan* man)
{
  cuddauxManRef(man);
  return man;
}

static inline void cuddauxCacheClear(struct CuddauxCache* cache)
{
  assert( (cache->cache==NULL)==(cache->man==NULL) );
  if (cache->cache){
    cuddLocalCacheQuit(cache->cache);
    cuddauxManFree(cache->man);
    cache->cache = NULL;
    cache->man = NULL;
  }
}
static inline void cuddauxCacheFree(struct CuddauxCache* cache)
{ cuddauxCacheClear(cache); free(cache); }
static inline void cuddauxHashClear(struct CuddauxHash* hash)
{
  assert( (hash->hash==NULL)==(hash->man==NULL) );
  if (hash->hash){
    cuddHashTableQuit(hash->hash);
    cuddauxManFree(hash->man);
    hash->hash = NULL;
    hash->man = NULL;
  }
}
static inline void cuddauxHashFree(struct CuddauxHash* hash)
{ cuddauxHashClear(hash); free(hash); }

static inline void cuddauxCommonClear(struct common* common)
{
  switch (common->memo.discr){
  case Global:
    return;
  case Cache:
    return cuddauxCacheClear(common->memo.u.cache);
  case Hash:
    return cuddauxHashClear(common->memo.u.hash);
  default:
    abort();
  }
}
static inline void* cuddauxCommonReinit(struct common* common)
{
  switch (common->memo.discr){
  case Global:
    return common->man;
  case Cache:
    return cuddauxCacheReinit(common->man,common->memo.u.cache);
  case Hash:
    return cuddauxHashReinit(common->man,common->memo.u.hash);
  default:
    abort();
  }
}

static inline DdNode* cuddauxCommonLookup1(struct common* common, DdNode* f)
{
  DdNode* res = NULL;
  switch (common->memo.discr){
  case Global:
    res = cuddCacheLookup1(common->man->man,(void*)common->pid,f);
    break;
  case Cache:
    res = cuddLocalCacheLookup(common->memo.u.cache->cache,&f);
    break;
  case Hash:
    if (f->ref != 1)
      res = cuddHashTableLookup1(common->memo.u.hash->hash,f);
    break;
  default:
    abort();
  }
  return res;
}
static inline DdNode* cuddauxCommonLookup2(struct common* common, DdNode* f, DdNode* g)
{
  DdNode* res = NULL;
  switch (common->memo.discr){
  case Global:
    res = cuddCacheLookup2(common->man->man,(void*)common->pid,f,g);
    break;
  case Cache:
    {
      DdNode* tab[2];
      tab[0]=f;
      tab[1]=g;
      res = cuddLocalCacheLookup(common->memo.u.cache->cache,tab);
    }
    break;
  case Hash:
    if (f->ref != 1 || g->ref != 1)
      res = cuddHashTableLookup2(common->memo.u.hash->hash,f,g);
    break;
  default:
    abort();
  }
  return res;
}
static inline DdNode* cuddauxCommonLookup3(struct common* common, DdNode* f, DdNode* g, DdNode* h)
{
  DdNode* res = NULL;
  switch (common->memo.discr){
  case Global:
    res = cuddCacheLookup(common->man->man,(ptruint)common->pid,f,g,h);
    break;
  case Cache:
    {
      DdNode* tab[3];
      tab[0]=f;
      tab[1]=g;
      tab[2]=h;
      res = cuddLocalCacheLookup(common->memo.u.cache->cache,tab);
    }
    break;
  case Hash:
    if (f->ref != 1 || g->ref != 1 || h->ref != 1)
      res = cuddHashTableLookup3(common->memo.u.hash->hash,f,g,h);
    break;
  default:
    abort();
  }
  return res;
}

static inline DdNode* cuddauxCommonInsert1(struct common* common, DdNode* f, DdNode* res)
{
  switch (common->memo.discr){
  case Global:
    cuddCacheInsert1(common->man->man,(void*)common->pid,f,res);
    return res;
  case Cache:
    cuddLocalCacheInsert(common->memo.u.cache->cache,&f,res);
    return res;
  case Hash:
    if (f->ref != 1){
      ptrint fanout = (ptrint) f->ref;
      cuddSatDec(fanout);
      if (!cuddHashTableInsert1(common->memo.u.hash->hash,f,res,fanout)) {
	Cudd_RecursiveDeref(common->man->man, res);
	return(NULL);
      }
    }
    return res;
  default:
    abort();
  }
}
static inline DdNode* cuddauxCommonInsert2(struct common* common, DdNode* f, DdNode* g, DdNode* res)
{
  switch (common->memo.discr){
  case Global:
    cuddCacheInsert2(common->man->man,(void*)common->pid,f,g,res);
    return res;
  case Cache:
    {
      DdNode* tab[2];
      tab[0]=f;
      tab[1]=g;
      cuddLocalCacheInsert(common->memo.u.cache->cache,tab,res);
    }
    return res;
  case Hash:
    if (f->ref != 1 || g->ref != 1){
      ptrint fanout = (ptrint) f->ref * g->ref;
      cuddSatDec(fanout);
      if (!cuddHashTableInsert2(common->memo.u.hash->hash,f,g,res,fanout)) {
	Cudd_RecursiveDeref(common->man->man, res);
	return(NULL);
      }
    }
    return res;
  default:
    abort();
  }
}
static inline DdNode* cuddauxCommonInsert3(struct common* common, DdNode* f, DdNode* g, DdNode* h, DdNode* res)
{
  switch (common->memo.discr){
  case Global:
    cuddCacheInsert(common->man->man,(ptruint)common->pid,f,g,h,res);
    return res;
  case Cache:
    {
      DdNode* tab[3];
      tab[0]=f;
      tab[1]=g;
      tab[2]=h;
      cuddLocalCacheInsert(common->memo.u.cache->cache,tab,res);
    }
    return res;
  case Hash:
    if (f->ref != 1 || g->ref != 1 || h->ref != 1){
      ptrint fanout = (ptrint) f->ref * g->ref * h-> ref;
      cuddSatDec(fanout);
      if (!cuddHashTableInsert3(common->memo.u.hash->hash,f,g,h,res,fanout)) {
	Cudd_RecursiveDeref(common->man->man, res);
	return(NULL);
      }
    }
    return res;
  default:
    abort();
  }
}

#endif
