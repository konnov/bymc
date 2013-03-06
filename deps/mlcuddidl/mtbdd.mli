(** MTBDDs with OCaml values *)

(* This file is part of the MLCUDDIDL Library, released under LGPL license.
   Please read the COPYING file packaged in the distribution  *)

type 'a unique
  (** Type of unique representants of MTBDD leaves of type ['a].

      For technical reason, type ['a] should not be implemented as
      a custom block with finalization function. (This is checked
      and the program aborts with an error message).

      Use {!Mtbddc} module if your type does not fulfill this
      requirement.  [Mtbddc] modules automatically encapsulate the
      value into a ML type. *)

type 'a t = 'a unique Vdd.t
  (** Type of MTBDDs.

      Objects of this type contains both the top node of the MTBDD
      and the manager to which the node belongs. The manager can
      be retrieved with {!manager}. Objects of this type are
      automatically garbage collected.  *)

type 'a table = 'a unique PWeakke.t
  (** Hashtable to manage unique constants *)

val print_table :
  ?first:(unit, Format.formatter, unit) format ->
  ?sep:(unit, Format.formatter, unit) format ->
  ?last:(unit, Format.formatter, unit) format ->
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a table -> unit

val make_table : hash:('a -> int) -> equal:('a -> 'a -> bool) -> 'a table
  (** Building a table *)

val unique : 'a table -> 'a -> 'a unique
  (** Building a unique constant *)
val get : 'a unique -> 'a
  (** Type conversion (no computation) *)

(** Public type for exploring the abstract type [t] *)
type 'a mtbdd =
  | Leaf of 'a unique      (** Terminal value *)
  | Ite of int * 'a t * 'a t (** Decision on CUDD variable *)

(** We refer to the modules {!Add} and {!Vdd} for the description
    of the interface. *)

(* ====================================================== *)
(** {3 Extractors} *)
(* ====================================================== *)

external manager : 'a t -> Man.v Man.t = "camlidl_cudd_bdd_manager"
  (** Returns the manager associated to the MTBDD *)

external is_cst : 'a t -> bool = "camlidl_cudd_bdd_is_cst"
  (** Is the MTBDD constant ? *)

external topvar : 'a t -> int = "camlidl_cudd_bdd_topvar"
  (** Returns the index of the top node of the MTBDD (65535 for a
      constant MTBDD) *)

external dthen : 'a t -> 'a t = "camlidl_cudd_add_dthen"
  (** Returns the positive subnode of the MTBDD *)

external delse : 'a t -> 'a t = "camlidl_cudd_add_delse"
  (** Returns the negative subnode of the MTBDD *)

external cofactors : int -> 'a t -> 'a t * 'a t = "camlidl_cudd_add_cofactors"
  (** Returns the positive and negative cofactor of the MTBDD wrt
      the variable *)

external cofactor : 'a t -> Man.v Bdd.t -> 'a t = "camlidl_cudd_add_cofactor"
  (** [cofactor mtbdd cube] evaluates [mtbbdd] on the cube [cube] *)

val dval_u : 'a t -> 'a unique
val dval : 'a t -> 'a
  (** Returns the value of the assumed constant MTBDD *)

val inspect : 'a t -> 'a mtbdd
  (** Decompose the MTBDD *)

(* ====================================================== *)
(** {3 Supports} *)
(* ====================================================== *)

external support : 'a t -> Man.v Bdd.t = "camlidl_cudd_bdd_support"
external supportsize : 'a t -> int = "camlidl_cudd_bdd_supportsize"
external is_var_in : int -> 'a t -> bool = "camlidl_cudd_bdd_is_var_in"
external vectorsupport : 'a t array -> Man.v Bdd.t = "camlidl_cudd_bdd_vectorsupport"
external vectorsupport2 : Man.v Bdd.t array -> 'a t array -> Man.v Bdd.t = "camlidl_cudd_add_vectorsupport2"

(* ====================================================== *)
(** {3 Classical operations} *)
(* ====================================================== *)

val cst_u : Man.v Man.t -> 'a unique -> 'a t
val cst : Man.v Man.t -> 'a table -> 'a -> 'a t

external ite : Man.v Bdd.t -> 'a t -> 'a t -> 'a t = "camlidl_cudd_add_ite"
external ite_cst : Man.v Bdd.t -> 'a t -> 'a t -> 'a t option = "camlidl_cudd_add_ite_cst"
external eval_cst : 'a t -> Man.v Bdd.t -> 'a t option = "camlidl_cudd_add_eval_cst"
external compose : int -> Man.v Bdd.t -> 'a t -> 'a t = "camlidl_cudd_add_compose"
val vectorcompose: ?memo:Memo.t -> Man.v Bdd.t array -> 'a t -> 'a t

(* ====================================================== *)
(** {3 Logical tests} *)
(* ====================================================== *)

external is_equal : 'a t -> 'a t -> bool = "camlidl_cudd_bdd_is_equal"
external is_equal_when : 'a t -> 'a t -> Man.v Bdd.t -> bool = "camlidl_cudd_bdd_is_equal_when"


val is_eval_cst_u : 'a t -> Man.v Bdd.t -> 'a unique option
val is_ite_cst_u : Man.v Bdd.t -> 'a t -> 'a t -> 'a unique option
val is_eval_cst : 'a t -> Man.v Bdd.t -> 'a option
val is_ite_cst : Man.v Bdd.t -> 'a t -> 'a t -> 'a option

(* ====================================================== *)
(** {3 Structural information} *)
(* ====================================================== *)

external size : 'a t -> int = "camlidl_cudd_bdd_size"
external nbpaths : 'a t -> float = "camlidl_cudd_bdd_nbpaths"
external nbnonzeropaths : 'a t -> float = "camlidl_cudd_bdd_nbtruepaths"
external nbminterms : int -> 'a t -> float = "camlidl_cudd_bdd_nbminterms"
external density : int -> 'a t -> float = "camlidl_cudd_bdd_density"
external nbleaves : 'a t -> int = "camlidl_cudd_add_nbleaves"

(* ====================================================== *)
(** {3 Variable mapping} *)
(* ====================================================== *)

external varmap : 'a t -> 'a t = "camlidl_cudd_add_varmap"
val permute : ?memo:Memo.t -> 'a t -> int array -> 'a t

(* ====================================================== *)
(** {3 Iterators} *)
(* ====================================================== *)

val iter_cube_u : (Man.tbool array -> 'a unique -> unit) -> 'a t -> unit
val iter_cube : (Man.tbool array -> 'a -> unit) -> 'a t -> unit


external iter_node: ('a t -> unit) -> 'a t -> unit = "camlidl_cudd_iter_node"

(* ====================================================== *)
(** {3 Leaves and guards} *)
(* ====================================================== *)

external guard_of_node : 'a t -> 'a t -> Man.v Bdd.t = "camlidl_cudd_add_guard_of_node"
external guard_of_nonbackground : 'a t -> Man.v Bdd.t = "camlidl_cudd_add_guard_of_nonbackground"
val nodes_below_level: ?max:int -> 'a t -> int option -> 'a t array

(** Guard of the given leaf *)
val guard_of_leaf_u : 'a t -> 'a unique -> Man.v Bdd.t
val guard_of_leaf : 'a table -> 'a t -> 'a -> Man.v Bdd.t

(** Returns the set of leaf values (excluding the background value) *)
val leaves_u: 'a t -> 'a unique array
val leaves: 'a t -> 'a array

(** Picks (but not randomly) a non background leaf. Return [None] if the only leaf is the background leaf. *)
val pick_leaf_u : 'a t -> 'a unique
val pick_leaf : 'a t -> 'a

(** Returns the set of leaf values together with their guard in the ADD *)
val guardleafs_u : 'a t -> (Man.v Bdd.t * 'a unique) array
val guardleafs : 'a t -> (Man.v Bdd.t * 'a) array

(* ====================================================== *)
(** {3 Minimizations} *)
(* ====================================================== *)

external constrain: 'a t -> Man.v Bdd.t -> 'a t = "camlidl_cudd_add_constrain"
external tdconstrain: 'a t -> Man.v Bdd.t -> 'a t = "camlidl_cudd_add_tdconstrain"
external restrict: 'a t -> Man.v Bdd.t -> 'a t = "camlidl_cudd_add_restrict"
external tdrestrict : 'a t -> Man.v Bdd.t -> 'a t = "camlidl_cudd_add_tdrestrict"

(* ====================================================== *)
(** {3 Conversions} *)
(* ====================================================== *)

(* ====================================================== *)
(** {3 User operations} *)
(* ====================================================== *)

(**
Two options:
- By decomposition into guards and leafs: see module {!Mapleaf}
- By using CUDD cache: see module {!User}
*)

(* ====================================================== *)
(** {3 Miscellaneous} *)
(* ====================================================== *)

external transfer : 'a t -> Man.v Man.t -> 'a t = "camlidl_cudd_add_transfer"

(* ====================================================== *)
(** {3 Printing} *)
(* ====================================================== *)

val print__minterm:
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a t -> unit
val print_minterm:
  (Format.formatter -> int -> unit) ->
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a t -> unit
val print:
  (Format.formatter -> Man.v Bdd.t -> unit) ->
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a t -> unit
