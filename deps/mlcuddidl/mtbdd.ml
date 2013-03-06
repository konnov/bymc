(** MTBDDs with OCaml values *)

open Format

type 'a table = 'a PWeakke.t

type 'a unique = 'a

let print_table = PWeakke.print
let make_table
  ~(hash : 'leaf -> int)
  ~(equal : 'leaf -> 'leaf -> bool)
  :
  'leaf table
  =
  PWeakke.create hash equal 23

let unique (table:'a table) (elt:'a) : 'a unique =
  if Obj.is_int (Obj.repr elt) then
    elt
  else
    PWeakke.merge_map table elt Man.copy_shr

let get (leaf:'a unique) : 'a = leaf

type 'a mtbdd =
  'a Vdd.vdd =
  | Leaf of 'a
  | Ite of int * 'a Vdd.t * 'a Vdd.t

include Vdd

let dval_u = dval
let is_eval_cst_u = is_eval_cst
let is_ite_cst_u = is_ite_cst
let iter_cube_u = iter_cube
let guard_of_leaf_u = guard_of_leaf
let guard_of_leaf table dd leaf = guard_of_leaf_u dd (unique table leaf)
let leaves_u = leaves
let pick_leaf_u = pick_leaf
let guardleafs_u = guardleafs

let cst_u = cst
let cst cudd table v = cst cudd (unique table v)
