/**CFile***********************************************************************

  FileName    [cuddauxUtil.c]

  PackageName [cuddaux]

  Synopsis    [Manipulation of objects CuddauxMan, CuddauxCache, CuddauxHash.]

  Description [Miscellaneous operations.]

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

/* ********************************************************************** */
/* CuddauxMan */
/* ********************************************************************** */

void cuddauxManFree(struct CuddauxMan* man)
{
  assert(man->count>=1);
  if (man->count<=1){
    assert(Cudd_CheckZeroRef(man->man)==0);
    Cudd_Quit(man->man);
    free(man);
  }
  else if (man->count != SIZE_MAX)
    man->count--;
}

/* ********************************************************************** */
/* CuddauxCache */
/* ********************************************************************** */

DdLocalCache* cuddauxCacheReinit(struct CuddauxMan* man, struct CuddauxCache* cache)
{
  if (cache->cache && cache->cache->manager!=man->man){
    cuddauxCacheClear(cache);
  }
  if (cache->cache == NULL){
    cache->cache =
      cuddLocalCacheInit(man->man,
			 cache->arity,
			 cache->initialsize,
			 cache->maxsize);
    if (cache->cache == NULL)
      man->man->errorCode = CUDD_MEMORY_OUT;
    else
      cache->man = cuddauxManCopy(man);
  }
  return cache->cache;
}

/* ********************************************************************** */
/* CuddauxHash */
/* ********************************************************************** */

DdHashTable* cuddauxHashReinit(struct CuddauxMan* man, struct CuddauxHash* hash)
{
  if (hash->man && hash->man!=man){
    cuddauxHashClear(hash);
  }
  if (hash->hash == NULL){
    hash->hash =
      cuddHashTableInit(man->man,
			hash->arity,
			hash->initialsize);
    if (hash->hash == NULL)
      man->man->errorCode = CUDD_MEMORY_OUT;
    else
      hash->man = cuddauxManCopy(man);
  }
  return hash->hash;
}

/* ********************************************************************** */
/* common__t */
/* ********************************************************************** */

DdNode* cuddauxCommonLookupN(struct common* common, DdNode** tab)
{
  int i;
  bool maybe;
  DdNode* res = NULL;

  switch (common->arity){
  case 1:
    return cuddauxCommonLookup1(common,tab[0]);
  case 2:
    return cuddauxCommonLookup2(common,tab[0],tab[1]);
  case 3:
    return cuddauxCommonLookup3(common,tab[0],tab[1],tab[2]);
  default:
    switch (common->memo.discr){
    case Global:
      abort();
    case Cache:
      res = cuddLocalCacheLookup(common->memo.u.cache->cache,tab);
      break;
    case Hash:
      maybe = false;
      for (i=0;i<common->arity;i++){
	if (tab[i]->ref!=1){
	  maybe=true; break;
	}
      }
      if (maybe)
	res = cuddHashTableLookup(common->memo.u.hash->hash,tab);
      break;
    default:
      abort();
    }
  }
  return res;
}

DdNode* cuddauxCommonInsertN(struct common* common, DdNode** tab, DdNode* res)
{
  int i;
  ptrint fanout;
  switch (common->arity){
  case 1:
    return cuddauxCommonInsert1(common,tab[0],res);
  case 2:
    return cuddauxCommonInsert2(common,tab[0],tab[1],res);
  case 3:
    return cuddauxCommonInsert3(common,tab[0],tab[1],tab[2],res);
  default:
    switch (common->memo.discr){
    case Global:
      abort();
    case Cache:
      cuddLocalCacheInsert(common->memo.u.cache->cache,tab,res);
      return res;
      break;
    case Hash:
      fanout = 1;
      for (i=0;i<common->arity;i++){
	fanout *= tab[i]->ref;
	if (fanout >= DD_MAXREF){
	  fanout = DD_MAXREF;
	  break;
	}
      }
      if (fanout!=1){
	cuddSatDec(fanout);
	if (!cuddHashTableInsert(common->memo.u.hash->hash,tab,res,fanout)){
	  Cudd_RecursiveDeref(common->man->man, res);
	  return(NULL);
	}
      }
      return res;
      break;
    default:
      abort();
    }
  }
  return res;
}
