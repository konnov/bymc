/**CFile***********************************************************************

  FileName    [cuddauxTable.c]

  PackageName [cuddaux]

  Synopsis    [Allows to put pointers in constant ADD node]

  Description [Miscellaneous operations..]

	    External procedures included in this module:
		<ul>
		<li>
		</ul>
	    Internal procedures included in this module:
		<ul>
		<li>
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
#include "caml/memory.h"

extern intnat caml_stat_compactions;
static intnat old_compactions = -1;

typedef union myhack {
    value value;
    unsigned int bits[2];
} myhack;

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Checks the unique table for the existence of a constant node.]

  Description [Copy of cuddUniqueConst.
  Checks the unique table for the existence of a constant node.
  If it does not exist, it creates a new one.  Does not
  modify the reference count of whatever is returned.  A newly created
  internal node comes back with a reference count 0.  Returns a
  pointer to the new node.]

  SideEffects [None]

***************************************************************************/

DdNode *
Cuddaux_addCamlConst(DdManager * unique,
		     value value)
{
  CAMLparam1(value);
  int pos;
  DdNodePtr *nodelist;
  DdNode *looking;
  myhack split;

  if (
      value==((struct CuddauxDdNode*)unique->one)->type.value ||
      value==((struct CuddauxDdNode*)unique->zero)->type.value ||
      value==((struct CuddauxDdNode*)unique->plusinfinity)->type.value ||
      value==((struct CuddauxDdNode*)unique->minusinfinity)->type.value
      ){
    fprintf(stderr,"\ncuddaux/mlcuddidl: big problem: CAML value assimilated to ZERO, ONE, PLUS_INFINITY or MINUS_INFINITY double value\nContact Bertrand Jeannet\n");
    abort();
  }

#ifdef DD_UNIQUE_PROFILE
  unique->uniqueLookUps++;
#endif

  if (unique->constants.keys > unique->constants.maxKeys) {
    if (unique->gcEnabled && ((unique->dead > unique->minDead) ||
			      (10 * unique->constants.dead > 9 * unique->constants.keys))) {	/* too many dead */
      (void) cuddGarbageCollect(unique,1);
    } else {
      cuddauxAddCamlConstRehash(unique,1);
      old_compactions = caml_stat_compactions;
    }
  }

  if (0<=old_compactions && old_compactions < caml_stat_compactions){
    cuddauxAddCamlConstRehash(unique,0);
  }
  old_compactions = caml_stat_compactions;

  split.bits[0] = split.bits[1] = 0;
  split.value = value >> 2;
  pos = ddHash(split.bits[0], split.bits[1], unique->constants.shift);
  nodelist = unique->constants.nodelist;
  looking = nodelist[pos];

  while (looking != NULL) {
    if ( ((struct CuddauxDdNode*)looking)->type.value == value) {
      if (looking->ref == 0) {
	cuddReclaim(unique,looking);
      }
      goto Cuddaux_addCamlConst_exit;
    }
    looking = looking->next;
#ifdef DD_UNIQUE_PROFILE
    unique->uniqueLinks++;
#endif
  }

  unique->keys++;
  unique->constants.keys++;

  looking = cuddAllocNode(unique);
  if (looking == NULL) goto Cuddaux_addCamlConst_exit;
  looking->index = CUDD_CONST_INDEX;
  ((struct CuddauxDdNode*)looking)->type.value = value;
  if (Is_block(value))
    caml_register_global_root(&((struct CuddauxDdNode*)looking)->type.value);
  looking->next = nodelist[pos];
  nodelist[pos] = looking;

 Cuddaux_addCamlConst_exit:
  if (0){
    printf("Adding value %ld, %f, pos=%d, node=%p\n",
	   value, Double_val(value),pos,looking
	   );
  }
  CAMLreturnT(DdNode*,looking);

} /* end of cuddaux_addCamlConst */


/**Function********************************************************************

  Synopsis    [Free ADD OCaml value for enabling garbage collection.]

  Description []

  SideEffects [None]

  SeeAlso     []

******************************************************************************/

int Cuddaux_addCamlPreGC(DdManager* unique, const char* s, void* data)
{
  DdNodePtr	*nodelist;
  int		j;
  DdNode	*node;
  int		slots;

  if (unique->constants.dead == 0) return 1;

  nodelist = unique->constants.nodelist;
  slots = unique->constants.slots;
  for (j = 0; j < slots; j++) {
    node = nodelist[j];
    while (node != NULL) {
      if (node->ref == 0) {
	value value = ((struct CuddauxDdNode *)node)->type.value;
	if (0){
	  printf("Removing value %ld, %f, pos=%d, node=%p\n",
		 value, Double_val(value),j,node
		 );
	}
	if (value==((struct CuddauxDdNode*)unique->one)->type.value){
	  fprintf(stderr,"\ncuddaux/mlcuddidl: big problem: CAML value assimilated to ONE double value\nContact Bertrand Jeannet\n");
	  abort();
	}
	if (value==((struct CuddauxDdNode*)unique->zero)->type.value){
	  fprintf(stderr,"\ncuddaux/mlcuddidl: big problem: CAML value assimilated to ZERO double value\nContact Bertrand Jeannet\n");
	  abort();
	}
	if (value==((struct CuddauxDdNode*)unique->plusinfinity)->type.value){
	  fprintf(stderr,"\ncuddaux/mlcuddidl: big problem: CAML value assimilated to PLUS_INFINITY double value\nContact Bertrand Jeannet\n");
	  abort();
	}
	if (value==((struct CuddauxDdNode*)unique->minusinfinity)->type.value){
	  fprintf(stderr,"\ncuddaux/mlcuddidl: big problem: CAML value assimilated to MINUS_INFINITY double value\nContact Bertrand Jeannet\n");
	  abort();
	}
	if (Is_block(value))
	  caml_remove_global_root(&((struct CuddauxDdNode*)node)->type.value);
      }
      node = node->next;
    }
  }
  return 1;
}


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

void cuddauxAddCamlConstRehash(DdManager* unique, int offset)
{
  unsigned int slots, oldslots;
  int shift, oldshift;
  int j, pos;
  DdNodePtr *nodelist, *oldnodelist;
  DdNode *node, *next;
  DdNode *sentinel = &(unique->sentinel);
  myhack split;
  extern DD_OOMFP MMoutOfMemory;
  DD_OOMFP saveHandler;

  oldslots = unique->constants.slots;
  oldshift = unique->constants.shift;
  oldnodelist = unique->constants.nodelist;

  /* The constant subtable is never subjected to reordering.
  ** Therefore, when it is resized, it is because it has just
  ** reached the maximum load. We can safely just double the size,
  ** with no need for the loop we use for the other tables.
  */
  slots = oldslots << offset;
  shift = oldshift - offset;
  saveHandler = MMoutOfMemory;
  MMoutOfMemory = Cudd_OutOfMem;
  nodelist = ALLOC(DdNodePtr, slots);
  MMoutOfMemory = saveHandler;
  if (nodelist == NULL) {
    int j;
    (void) fprintf(unique->err,
		   "Unable to resize constant subtable for lack of memory\n");
    (void) cuddGarbageCollect(unique,1);
    for (j = 0; j < unique->size; j++) {
      unique->subtables[j].maxKeys <<= 1;
    }
    unique->constants.maxKeys <<= 1;
    return;
  }
  unique->constants.slots = slots;
  unique->constants.shift = shift;
  unique->constants.maxKeys = slots * DD_MAX_SUBTABLE_DENSITY;
  unique->constants.nodelist = nodelist;
  for (j = 0; (unsigned) j < slots; j++) {
    nodelist[j] = NULL;
  }
  for (j = 0; (unsigned) j < oldslots; j++) {
    node = oldnodelist[j];
    while (node != NULL) {
      next = node->next;
      split.bits[0] = split.bits[1] = 0;
      split.value = cuddauxCamlV(node) >> 2;
      pos = ddHash(split.bits[0], split.bits[1], shift);
      node->next = nodelist[pos];
      nodelist[pos] = node;
      node = next;
    }
  }
  FREE(oldnodelist);

#ifdef DD_VERBOSE
  (void) fprintf(unique->err,
		 "rehashing constants: keys %d dead %d new size %d\n",
		 unique->constants.keys,unique->constants.dead,slots);
#endif
}
