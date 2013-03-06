dnl This file is part of the MLCUDDIDL Library, released under LGPL license.
dnl Please read the COPYING file packaged in the distribution
dnl
changequote([[, ]])dnl
dnl
dnl
dnl ***************************************************************************
dnl Macros to wrap the transformation DdNode* en node__t
dnl ***************************************************************************
dnl
dnl Unary operations: name of the arg. of type node__t is no,
dnl Binary operations: no1, no2
dnl Ternary operations: no1,no2,no3
dnl
dnl ===========================================================================
dnl Check identity of the managers
dnl ===========================================================================
dnl
define([[CHECK_MAN2]],
[[if (no1.man!=no2.man){ \
  caml_invalid_argument(\"Dd: binary function called with nodes belonging to different managers !\"); \
}]])dnl
dnl
define([[CHECK_MAN3]],
[[if (no1.man!=no2.man || no1.man!=no3.man){ \
  caml_invalid_argument(\"Dd: ternary function called with nodes belonging to different managers !\"); \
}]])dnl
dnl
dnl ===========================================================================
dnl Macros for calling sequences
dnl ===========================================================================
dnl
dnl The number(s) indicates in which order the arguments are applied
dnl
define([[VAL_OF_MAN]],
[[quote(call, "
Begin_roots1(_v_man);
_res = $1(man->man);
End_roots();
")]])dnl
define([[UNIT_OF_MAN_VAL]],
[[quote(call, "
Begin_roots1(_v_man);
$1(man->man,v);
End_roots();
")]])dnl
define([[NO_OF_NO]],
[[quote(call, "
Begin_roots1(_v_no);
_res.man = no.man;
_res.node = $1(no.node);
End_roots();
")]])dnl
define([[NO_OF_MAN_NO]],
[[quote(call, "
Begin_roots1(_v_no);
_res.man = no.man;
_res.node = $1(no.man->man,no.node);
End_roots();
")]])dnl
define([[NO_OF_MAN_NO12]],
[[quote(call,
"CHECK_MAN2();
Begin_roots2(_v_no1,_v_no2);
_res.man = no1.man;
_res.node = $1(no1.man->man,no1.node,no2.node);
End_roots();
")]])dnl
define([[NO_OF_MAN_NO21]],
[[quote(call,
"CHECK_MAN2();
Begin_roots2(_v_no1,_v_no2);
_res.man = no1.man;
_res.node = $1(no1.man->man,no2.node,no1.node);
End_roots();
")]])dnl
define([[NO_OF_MAN_NO123]],
[[quote(call,
"CHECK_MAN3();
Begin_roots3(_v_no1,_v_no2,_v_no3);
_res.man = no1.man;
_res.node = $1(no1.man->man,no1.node,no2.node,no3.node);
End_roots();
")]])dnl
define([[NO_OF_MAN_NO231]],
[[quote(call,
"CHECK_MAN3();
Begin_roots3(_v_no1,_v_no2,_v_no3);
_res.man = no1.man;
_res.node = $1(no1.man->man,no2.node,no3.node,no1.node);
End_roots();
")]])dnl
dnl
dnl ===========================================================================
dnl Macro for subset or superset approximation functions on BDDs
dnl ===========================================================================
dnl
define([[SUBSUPERSET]],
[[quote(call,"
Begin_roots1(_v_no);
_res.man=no.man; _res.node = $1(no.man->man,no.node,nvars,threshold);
End_roots();
")]])dnl
dnl
dnl ===========================================================================
dnl Macro for decomposition functions on BDDs
dnl ===========================================================================
dnl
define([[DECOMP]],[[
quote(MLI,"(** [$2]. *)")
quote(MLMLI,"external $1: 'a t -> ('a t * 'a t) option = \"camlidl_bdd_$1\"")
quote(C,"
value camlidl_bdd_$1(value _v_no)
{
  CAMLparam1(_v_no); CAMLlocal4(_v_res,_v_a,_v_b,_v_pair);
  bdd__t no;
  int res;
  DdNode** tab;
  bdd__t a;
  bdd__t b;

  camlidl_cudd_node_ml2c(_v_no,&no);
  res = $2(no.man->man,no.node,&tab);
  switch(res){
  case 0:
    caml_failwith(\"Bdd.$1: decomposition function failed (probably CUDD_OUT_OF_MEM)\");
    break;
  case 1:
    _v_res = Val_int(0);
    cuddDeref(tab[0]);
    free(tab);
    break;
  case 2:
    a.man = b.man = no.man;
    a.node = tab[0];
    b.node = tab[1];
    cuddDeref(a.node);
    _v_a = camlidl_cudd_bdd_c2ml(&a);
    cuddDeref(b.node);
    _v_b = camlidl_cudd_bdd_c2ml(&b);
    _v_pair = alloc_small(0,2);
    Field(_v_pair,0) = _v_a;
    Field(_v_pair,1) = _v_b;
    _v_res = alloc_small(0,1);
    Field(_v_res,0) = _v_pair;
    free(tab);
    break;
  }
  CAMLreturn(_v_res);
}")
]])dnl
dnl
dnl ===========================================================================
dnl Macro for applying unary and binary operations on ADDs
dnl ===========================================================================
dnl
define([[APPLYBINOP]],[[quote(call,
"CHECK_MAN2();
Begin_roots2(_v_no1,_v_no2);
_res.man = no1.man;
_res.node = Cudd_addApply(no1.man->man,$1,no1.node,no2.node);
End_roots();
")]])dnl
dnl
define([[APPLYUNOP]],[[quote(call,"
Begin_roots1(_v_no);
_res.man = no.man;
_res.node = Cudd_addMonadicApply(no.man->man,$1,no.node);
End_roots();
")]])dnl
dnl
dnl
dnl ***************************************************************************
dnl Macros for matrix multiplication on ADDs
dnl ***************************************************************************
dnl
define([[MATMUL]],[[
value $1(value _v_array, value _v_no1, value _v_no2)
{
  CAMLparam3(_v_array,_v_no1,_v_no2); CAMLlocal1(_v_res);
  int i,size;
  DdNode** array;
  node__t no,no1,no2;

  camlidl_cudd_node_ml2c(_v_no1,&no1);
  camlidl_cudd_node_ml2c(_v_no2,&no2);
  CHECK_MAN2();
  size = Wosize_val(_v_array);
  array = malloc(size * sizeof(DdNode*));
  for (i=0; i<size; i++){
    value _v_index = Field(_v_array,i);
    int index = Int_val(_v_index);
    array[i] = Cudd_bddIthVar(no1.man->man, index);
  }
  no.man = no1.man;
  no.node = $2(no1.man->man,no1.node,no2.node,array,size);
  _v_res = camlidl_cudd_node_c2ml(&no);
  free(array);
  CAMLreturn(_v_res);
}]])dnl
dnl
