(** MTBDDs with finalized OCaml values. *)

open Format

type 'a capsule = {
  content : 'a
}
type 'a unique = 'a capsule

type 'a table = 'a capsule PWeakke.t

type 'a t = 'a capsule Vdd.t

let print_table ?first ?sep ?last print fmt table =
  PWeakke.print ?first ?sep ?last
    (fun fmt x -> print fmt x.content) fmt table

let make_table
  ~(hash : 'leaf -> int)
  ~(equal : 'leaf -> 'leaf -> bool)
  :
  'leaf table
  =
  let hash x = hash x.content in
  let equal x y = x==y || equal x.content y.content in
  PWeakke.create hash equal 23

let unique (table:'a table) (elt:'a) : 'a capsule =
  PWeakke.merge_map table {content=elt} Man.copy_shr

let get (leaf:'a capsule) : 'a = leaf.content

(** Public type for exploring the abstract type [t] *)
type 'a mtbdd =
  | Leaf of 'a unique        (** Terminal value *)
  | Ite of int * 'a t * 'a t (** Decision on CUDD variable *)

external manager : 'a t -> Man.v Man.t = "camlidl_cudd_bdd_manager"
external is_cst : 'a t -> bool = "camlidl_cudd_bdd_is_cst"
external topvar : 'a t -> int = "camlidl_cudd_bdd_topvar"
external dthen : 'a t -> 'a t = "camlidl_cudd_add_dthen"
external delse : 'a t -> 'a t = "camlidl_cudd_add_delse"
external cofactors : int -> 'a t -> 'a t * 'a t
  = "camlidl_cudd_add_cofactors"
external cofactor : 'a t -> Man.v Bdd.t -> 'a t = "camlidl_cudd_add_cofactor"
let dval_u = Vdd.dval
let dval t = get (dval_u t)
let inspect t = match Vdd.inspect t with
  | Vdd.Leaf xu -> Leaf xu
  | Vdd.Ite(a,b,c) -> Ite(a,b,c)
external support : 'a t -> Man.v Bdd.t = "camlidl_cudd_bdd_support"
external supportsize : 'a t -> int = "camlidl_cudd_bdd_supportsize"
external is_var_in : int -> 'a t -> bool = "camlidl_cudd_bdd_is_var_in"
external vectorsupport : 'a t array -> Man.v Bdd.t
  = "camlidl_cudd_bdd_vectorsupport"
external vectorsupport2 : Man.v Bdd.t array -> 'a t array -> Man.v Bdd.t
  = "camlidl_cudd_add_vectorsupport2"
let cst_u = Vdd.cst
let cst cudd table x = Vdd.cst cudd (unique table x)
let _background = Vdd._background
external ite : Man.v Bdd.t -> 'a t -> 'a t -> 'a t = "camlidl_cudd_add_ite"
external ite_cst : Man.v Bdd.t -> 'a t -> 'a t -> 'a t option
  = "camlidl_cudd_add_ite_cst"
external eval_cst : 'a t -> Man.v Bdd.t -> 'a t option
  = "camlidl_cudd_add_eval_cst"
external compose : int -> Man.v Bdd.t -> 'a t -> 'a t
  = "camlidl_cudd_add_compose"
external vectorcompose : Man.v Bdd.t array -> 'a t -> 'a t
  = "camlidl_cudd_add_vectorcompose"
external is_equal : 'a t -> 'a t -> bool = "camlidl_cudd_bdd_is_equal"
external is_equal_when : 'a t -> 'a t -> Man.v Bdd.t -> bool
  = "camlidl_cudd_bdd_is_equal_when"
let is_eval_cst_u = Vdd.is_eval_cst
let is_ite_cst_u = Vdd.is_ite_cst
let is_eval_cst t bdd =
  match is_eval_cst_u t bdd with
  | None -> None
  | Some x -> Some (get x)
let is_ite_cst bdd t1 t2 =
  match is_ite_cst_u bdd t1 t2 with
  | None -> None
  | Some x -> Some (get x)
external size : 'a t -> int = "camlidl_cudd_bdd_size"
external nbpaths : 'a t -> float = "camlidl_cudd_bdd_nbpaths"
external nbnonzeropaths : 'a t -> float = "camlidl_cudd_bdd_nbtruepaths"
external nbminterms : int -> 'a t -> float = "camlidl_cudd_bdd_nbminterms"
external density : int -> 'a t -> float = "camlidl_cudd_bdd_density"
external nbleaves : 'a t -> int = "camlidl_cudd_add_nbleaves"
external varmap : 'a t -> 'a t = "camlidl_cudd_add_varmap"
external permute : 'a t -> int array -> 'a t = "camlidl_cudd_add_permute"
let iter_cube_u = Vdd.iter_cube
let iter_cube f t =
  iter_cube_u
    (fun minterm xu -> f minterm (get xu))
    t
external iter_node : ('a t -> unit) -> 'a t -> unit
  = "camlidl_cudd_iter_node"
external guard_of_node : 'a t -> 'a t -> Man.v Bdd.t
  = "camlidl_cudd_add_guard_of_node"
external guard_of_nonbackground : 'a t -> Man.v Bdd.t
  = "camlidl_cudd_add_guard_of_nonbackground"
let nodes_below_level = Vdd.nodes_below_level
let guard_of_leaf_u = Vdd.guard_of_leaf
let guard_of_leaf table dd leaf = guard_of_leaf_u dd (unique table leaf)

let leaves_u = Vdd.leaves
let leaves t = Array.map get (leaves_u t)

let pick_leaf_u = Vdd.pick_leaf
let pick_leaf t = get (pick_leaf_u t)
let guardleafs_u = Vdd.guardleafs
let guardleafs t =
  Array.map (fun (g,xu) -> (g,get xu)) (guardleafs_u t)
external constrain : 'a t -> Man.v Bdd.t -> 'a t
  = "camlidl_cudd_add_constrain"
external tdconstrain : 'a t -> Man.v Bdd.t -> 'a t
  = "camlidl_cudd_add_tdconstrain"
external restrict : 'a t -> Man.v Bdd.t -> 'a t = "camlidl_cudd_add_restrict"
external tdrestrict : 'a t -> Man.v Bdd.t -> 'a t
  = "camlidl_cudd_add_tdrestrict"

external transfer : 'a t -> Man.v Man.t -> 'a t = "camlidl_cudd_add_transfer"
let print__minterm print_leaf fmt t =
  Vdd.print__minterm (fun fmt x -> print_leaf fmt x.content) fmt t
let print_minterm print_id print_leaf fmt t =
  Vdd.print_minterm print_id (fun fmt x -> print_leaf fmt x.content) fmt t
let print print_bdd print_leaf fmt t =
  Vdd.print print_bdd (fun fmt x -> print_leaf fmt x.content) fmt t
