/* Conversion of datatypes and common functions */

/* This file is part of the MLCUDDIDL Library, released under LGPL license.
   Please read the COPYING file packaged in the distribution  */

#ifndef __CUDD_CAML_H__
#define __CUDD_CAML_H__

#include <stdio.h>
#include <assert.h>

#include "cuddInt.h"
#include "cuddaux.h"

#include "caml/mlvalues.h"

typedef value mlvalue;

typedef struct CuddauxMan* man__t;
typedef struct CuddauxMan* man__dt;
typedef struct CuddauxMan* man__vt;

typedef struct CuddauxHash* hash__t;
typedef struct CuddauxCache* cache__t;
typedef struct node__t bdd__t;
typedef struct node__t bdd__dt;
typedef struct node__t bdd__vt;
typedef struct node__t node__t;
typedef struct node__t add__t;
typedef struct node__t vdd__t;
typedef struct node__t mtbdd__t;


static inline void camlidl_cudd_man_ml2c(value val, struct CuddauxMan** man)
{ *man = *((struct CuddauxMan**)(Data_custom_val(val))); }
static inline void camlidl_cudd_hash_ml2c(value val, struct CuddauxHash** hash)
{ *hash = *((struct CuddauxHash**)(Data_custom_val(val))); }
static inline void camlidl_cudd_cache_ml2c(value val, struct CuddauxCache** cache)
{ *cache = *((struct CuddauxCache**)(Data_custom_val(val))); }
static inline void camlidl_cudd_pid_ml2c(value val, pid* ppid)
{ *ppid = *((void**)(Data_custom_val(val))); }
static inline void camlidl_cudd_node_ml2c(value val, struct node__t* node)
{*node = *(node__t*)(Data_custom_val(val)); }

value camlidl_cudd_man_c2ml(struct CuddauxMan** man);
value camlidl_cudd_hash_c2ml(struct CuddauxHash** hash);
value camlidl_cudd_cache_c2ml(struct CuddauxCache** cache);
value camlidl_cudd_pid_c2ml(pid* pid);
value camlidl_cudd_node_c2ml(struct node__t* no);
value camlidl_cudd_bdd_c2ml(struct node__t* bdd);

static inline void camlidl_cudd_mlvalue_ml2c(value val, value* p)
{ *p = val; }
static inline value camlidl_cudd_mlvalue_c2ml(value* p)
{ return *p; }

#define man_of_vmanager(x) (*(struct CuddauxMan**)(Data_custom_val(x)))
#define DdManager_of_vmanager(x) (*(struct CuddauxMan**)(Data_custom_val(x)))->man

#define node_of_vnode(x) ((node__t*)(Data_custom_val(x)))
#define DdManager_of_vnode(x) ((node__t*)(Data_custom_val(x)))->man->man
#define DdNode_of_vnode(x) ((node__t*)(Data_custom_val(x)))->node

value camlidl_cudd_set_gc(value _v_heap, value _v_gc, value _v_reordering);
int camlidl_cudd_garbage(DdManager* dd, const char* s, void* data);
int camlidl_cudd_reordering(DdManager* dd, const char* s, void* data);
value camlidl_cudd_custom_copy_shr(value arg);

value camlidl_cudd_bdd_inspect(value vno);
value camlidl_cudd_bdd_cofactors(value v_var, value v_no);
value camlidl_cudd_add_cofactors(value v_var, value v_no);

value camlidl_cudd_avdd_dval(value vno);
value camlidl_cudd_avdd_cst(value vman, value vleaf);
value camlidl_cudd_avdd_inspect(value vno);
value camlidl_cudd_avdd_is_eval_cst(value vno1, value vno2);
value camlidl_cudd_avdd_is_ite_cst(value vno1, value vno2, value vno3);
value camlidl_cudd_list_of_support(value _v_no);
value camlidl_cudd_invalid_exception(const char* msg);
man__t camlidl_cudd_tnode_ml2c(value _v_vec, int size, DdNode** vec);
value camlidl_cudd_tnode_c2ml(man__t man, DdNode** vec, int size);
value camlidl_cudd_bdd_vectorsupport(value _v_vec);
value camlidl_cudd_add_vectorsupport2(value _v_vec1, value _v_vec2);

value camlidl_cudd_abdd_vectorcompose(bool bdd, value _v_vec, value _v_no);
value camlidl_cudd_bdd_vectorcompose(value _v_vec, value _v_no);
value camlidl_cudd_add_vectorcompose(value _v_vec, value _v_no);

value camlidl_cudd_abdd_vectorcompose_memo(bool bdd, value _v_memo,value _v_vec, value _v_no);
value camlidl_cudd_bdd_vectorcompose_memo(value _v_memo,value _v_vec, value _v_no);
value camlidl_cudd_add_vectorcompose_memo(value _v_memo,value _v_vec, value _v_no);
value camlidl_cudd_abdd_permute(bool bdd, value _v_no, value _v_permut);
value camlidl_cudd_bdd_permute(value _v_no, value _v_permut);
value camlidl_cudd_add_permute(value _v_no, value _v_permut);
value camlidl_cudd_abdd_permute_memo(bool bdd, value _v_memo, value _v_no, value _v_permut);
value camlidl_cudd_bdd_permute_memo(value _v_memo, value _v_no, value _v_permut);
value camlidl_cudd_add_permute_memo(value _v_memo, value _v_no, value _v_permut);

value camlidl_cudd_iter_node(value _v_closure, value _v_no);
value camlidl_cudd_bdd_iter_cube(value _v_closure, value _v_no);
value camlidl_cudd_avdd_iter_cube(value _v_closure, value _v_no);
value camlidl_cudd_bdd_iter_prime(value _v_closure, value _v_lower, value _v_upper);
value camlidl_cudd_cube_of_bdd(value _v_no);
value camlidl_cudd_cube_of_minterm(value _v_man, value _v_array);
value camlidl_cudd_list_of_cube(value _v_no);
value camlidl_cudd_pick_minterm(value _v_no);
int array_of_support(DdManager* man, DdNode* supp, DdNode*** pvars, int* psize);
value camlidl_cudd_pick_cube_on_support(value _v_no1, value _v_no2);
value camlidl_cudd_pick_cubes_on_support(value _v_no1, value _v_no2, value _v_k);
value camlidl_cudd_avdd_guard_of_leaf(value _v_no, value _v_leaf);
value camlidl_cudd_avdd_nodes_below_level(value _v_no, value _v_olevel, value _v_omax);
value camlidl_cudd_avdd_leaves(value _v_no);
value camlidl_cudd_avdd_pick_leaf(value _v_no);
value camlidl_cudd_print(value _v_no);

DdNode* camlidl_cudd_custom_op1(DdManager* dd, struct op1* op, DdNode* node);
DdNode* camlidl_cudd_custom_op2(DdManager* dd, struct op2* op, DdNode* node1, DdNode* node2);
DdNode* camlidl_cudd_custom_op3(DdManager* dd, struct op3* op, DdNode* node1, DdNode* node2, DdNode* node3);
DdNode* camlidl_cudd_custom_opNG(DdManager* dd, struct opN* op, DdNode** node);
int camlidl_cudd_custom_opGbeforeRec(DdManager* dd, struct opG* op, DdNode* no, DdNode** tnode);
DdNode* camlidl_cudd_custom_opGite(DdManager* dd, struct opG* op, int index, DdNode* T, DdNode* E);
DdNode* camlidl_cudd_custom_test2(DdManager* dd, struct test2* op, DdNode* node1, DdNode* node2);

#endif
