(** Custom operations for MTBDDs *)

(** Important note: The OCaml closure defining the custom
    operation should not use free variables that may be modified
    and so impact its result: they would act as hidden parameters
    that are not taken into account in the memoization table.

    If such hidden parameters are modified, the cache should be
    cleared with [Memo.clear], if it is local, otherwise the global
    cache should be cleared with {!Man.flush}. *)

(*  ********************************************************************** *)
(** {3 Types and values} *)
(*  ********************************************************************** *)

(*  ====================================================================== *)
(** {4 Type of registered operations} *)
(*  ====================================================================== *)

(** Identifiers of closures used in shared memoization tables *)
type pid = Custom.pid

(** Common information to all operations *)
type common = Custom.common = {
  pid: pid;
    (** Identifiers for shared memoization tables *)
  arity: int;
    (** Arity of the operations *)
  memo: Memo.t;
    (** Memoization table *)
}

val newpid : unit -> Custom.pid
val make_common : ?memo:Memo.t -> int -> common

(*  ********************************************************************** *)
(** {3 Unary operations} *)
(*  ********************************************************************** *)

type ('a,'b) op1 = ('a,'b) Custom.op1 = private {
  common1: common;
  closure1: 'a -> 'b;
    (** Operation on leaves *)
}
val make_op1 : ?memo:Memo.t -> ('a -> 'b) -> ('a, 'b) op1
  (** Makes a binary operation, with the given memoization policy. *)
val apply_op1 : ('a, 'b) op1 -> 'a Vdd.t -> 'b Vdd.t


(** {5 Example:}

    Assuming [type t = bool Vdd.t], and corresponding diagrams
    [bdd:t] and [bdd2:t] (with type [bool], it is safe to use
    directly VDDs, and it simplifies the examples).

    We want to negate every leaf of [bdd1] and [bdd2].

    {ul
    {- We register the operation:

    [let op = make_op1 ~memo:(Cache (Cache.create 1)) (fun b -> not b);;]
    }
    {- Later we apply it on [bdd1] and [bdd2] with

    [let res1 = apply_op1 op bdd1 and res2 = apply_op1 op bdd2;;]
    }
    {- The local cache is reused between the two calls to
    [apply_op1], which is nice if [bdd1] and [bdd2] share common
    nodes. The cache is automatically garbage collected when
    needed.  But even if diagrams in the caches entries may be
    garbage collected, the cache itself takes memory. You can
    clear it with [Cache.clear] or [Memo.clear].  }
    {- If [~memo::(Cache (Cache.create 1))] is replaced by
    [~memo::(Hash (Hash.create 1))], then diagrams in the table
    are referenced and cannot be gabage collected.  You should
    clear them explicitly with [Hash.clear] or [Memo.clear].  }
    {- The third option is to use the CUDD global regular cache,
    which is automatically garbage collected when needed:
    }
    {- If the operation is applied only once to one diagram, it is simpler to write
    [let res1 = map_op1 (fun b -> not b) bdd1;;]
    }
    }
*)

(*  ********************************************************************** *)
(** {3 Binary operations} *)
(*  ********************************************************************** *)

type ('a,'b,'c) op2 = ('a,'b,'c) Custom.op2 = private {
  common2: common;
  closure2: 'a -> 'b -> 'c;
    (** Operation on leaves *)
  ospecial2: ('a Vdd.t -> 'b Vdd.t -> 'c Vdd.t option) option;
    (** Special case operation *)
  commutative: bool;
    (** Is the operation commutative ? *)
  idempotent: bool;
    (** Is the operation idempotent ([op x x = x]) ? *)
}
val make_op2 :
  ?memo:Memo.t ->
  ?commutative:bool ->
  ?idempotent:bool ->
  ?special:('a Vdd.t -> 'b Vdd.t -> 'c Vdd.t option) ->
  ('a -> 'b -> 'c) -> ('a, 'b, 'c) op2
  (** Makes a binary operation, with the given memoization policy.

      [commutative] (default: [false]), when [true], allows to
      optimize the cache usage (hence the speed) when the operation
      is commutative.

      [idempotent] (default: [false]) allows similarly some
      optimization when op is idempotent: [op x x = x].
      This makes sense only if ['a='b='c] (the case will never
      happens otherwise).

      [?special] (default: [None]), if equal to [Some
      specialcase], modifies [op] as follows: it is applied to
      every pair of node during the recursive descend, and if
      [specialcase vdda vddb = (Some vddc)], then [vddc] is
      assumed to be the result of [map_op2 op vdda vddb].  This
      allows not to perform a full recursive descend when a
      special case is encountered. See the example below.
  *)
val apply_op2 : ('a, 'b, 'c) op2 -> 'a Vdd.t -> 'b Vdd.t -> 'c Vdd.t

(** {5 Example:}

    Assuming as for unary operation example [type t = bool Vdd.t]
    and corresponding diagrams [bdd1:t] and [bdd2:t].

    We can compute their conjunction with

    {[let res = map_op2
  ~commutative:true ~idempotent:true
  ~special:(fun bdd1 bdd2 ->
    if Vdd.is_cst bdd1 && Vdd.dval bdd1 = false then Some(bdd1)
    else if Vdd.is_cst bdd2 && Vdd.dval bdd2 = false then Some(bdd2)
    else None
  (fun b1 b2 -> b1 && b2) bdd1 bdd2;;]}
*)

(*  ********************************************************************** *)
(** {3 Ternary operations} *)
(*  ********************************************************************** *)

type ('a,'b,'c,'d) op3 = ('a,'b,'c,'d) Custom.op3 = private {
  common3: common;
  closure3: 'a -> 'b -> 'c -> 'd;
    (** Operation on leaves *)
  ospecial3: ('a Vdd.t -> 'b Vdd.t -> 'c Vdd.t -> 'd Vdd.t option) option;
    (** Special cases *)
}
val make_op3 :
  ?memo:Memo.t ->
  ?special:('a Vdd.t -> 'b Vdd.t -> 'c Vdd.t -> 'd Vdd.t option) ->
  ('a -> 'b -> 'c -> 'd) -> ('a, 'b, 'c, 'd) op3
val apply_op3 :
  ('a, 'b, 'c, 'd) op3 -> 'a Vdd.t -> 'b Vdd.t -> 'c Vdd.t -> 'd Vdd.t
  (** Combine the two previous operations.
      if [?memo=None], then a hash table is used, and cleared at the end. *)

(** {5 Example:}

    Still assuming [type t = bool Vdd.t]
    and corresponding diagrams [bdd1:t], [bdd2:t], [bdd3:t].

    We can define [if-then-else] with
{[let res = map_op3
  ~special:(fun bdd1 bdd2 bdd3 ->
    if Vdd.is_cst bdd1
    then Some(if Vdd.dval bdd1 (* = true *) then bdd2 else bdd3)
    else None
  )
  (fun b1 b2 b3 -> if b1 then b2 else b3) bdd1 bdd2 bdd3]}
*)

(*  ********************************************************************** *)
(** {3 Nary operations} *)
(*  ********************************************************************** *)

(** N-ary operation *)
type ('a,'b) opN = ('a,'b) Custom.opN = private {
  commonN: common;
  arityNbdd : int;
  closureN: Bdd.vt array -> 'a Vdd.t array -> 'b Vdd.t option;
    (** Operation on leaves *)
}
val make_opN :
  ?memo:Memo.t ->
  int -> int ->
  (Bdd.vt array -> 'a Vdd.t array -> 'b Vdd.t option) ->
  ('a, 'b) opN
val apply_opN : ('a, 'b) opN -> Bdd.vt array -> 'a Vdd.t array -> 'b Vdd.t

(** N-ary general operation *)
type ('a,'b) opG = ('a,'b) Custom.opG = private {
  commonG: common;
  arityGbdd: int;
  closureG: Bdd.vt array -> 'a Vdd.t array -> 'b Vdd.t option;
  oclosureBeforeRec: (int*bool -> Bdd.vt array -> 'a Vdd.t array -> (Bdd.vt array * 'a Vdd.t array)) option;
  oclosureIte: (int -> 'b Vdd.t -> 'b Vdd.t -> 'b Vdd.t) option;
}
val make_opG :
  ?memo:Memo.t ->
  ?beforeRec:(int*bool -> Bdd.vt array -> 'a Vdd.t array -> (Bdd.vt array * 'a Vdd.t array)) ->
  ?ite:(int -> 'b Vdd.t -> 'b Vdd.t -> 'b Vdd.t) ->
  int -> int ->
  (Bdd.vt array -> 'a Vdd.t array -> 'b Vdd.t option) ->
  ('a, 'b) opG
val apply_opG : ('a, 'b) opG -> Bdd.vt array -> 'a Vdd.t array -> 'b Vdd.t

(*  ********************************************************************** *)
(** {3 Binary tests} *)
(*  ********************************************************************** *)

type ('a,'b) test2 = ('a,'b) Custom.test2 = private {
  common2t: common;
  closure2t: 'a -> 'b -> bool;
    (** Test on leaves *)
  ospecial2t: ('a Vdd.t -> 'b Vdd.t -> bool option) option;
    (** Special cases *)
  symetric: bool;
    (** Is the relation symetric ? *)
  reflexive: bool;
    (** Is the relation reflexive ? ([test x x = true]) ? *)
}
val make_test2 :
  ?memo:Memo.t ->
  ?symetric:bool ->
  ?reflexive:bool ->
  ?special:('a Vdd.t -> 'b Vdd.t -> bool option) ->
  ('a -> 'b -> bool) -> ('a, 'b) test2
  (** Register a binary test, with the given memoization policy,

      [symetric] (default: [false]), when [true], allows to
      optimize the cache usage (hence the speed) when the relation is symetric.

      [reflexive] (default: [false]) allows similarly some
      optimization when the relation is reflexive: [test x x = true].
      This makes sense only if ['a='b] (the case will never
      happen otherwise).

      [?special] (default: [None]) has the same semantics as for
      binary operation above.
  *)
val apply_test2 : ('a, 'b) test2 -> 'a Vdd.t -> 'b Vdd.t -> bool

(*  ********************************************************************** *)
(** {3 Quantification} *)
(*  ********************************************************************** *)

type 'a exist = 'a Custom.exist = private {
  commonexist: common;
  combineexist: ('a,'a,'a) op2;
    (** Combining operation when a decision is eliminated *)
}
val make_exist : ?memo:Memo.t -> ('a, 'a, 'a) op2 -> 'a exist
  (** Make an existential quantification operation, with the given
      memoization policy, and the given underlying binary
      operation, assumed to be commutative and idempotent, that
      combines the two branch of the diagram when a decision is
      quantified out. *)

val apply_exist : 'a exist -> supp:Bdd.vt -> 'a Vdd.t -> 'a Vdd.t

(** {5 Example:}

    Still assuming [type t = bool Vdd.t]
    and corresponding diagrams [bdd:t]

    We define ordinary existential quantification with

{[let dor = make_op2 ~commutative:true ~idempotent:true ( || );;
let exist = make_exist dor;;
let res = apply_exist exist ~supp bdd;;
]}

    We can define ordinary universal quantification by replacing
    [||] with [&&].
*)

(*  ********************************************************************** *)
(** {3 Quantification combined with intersection} *)
(*  ********************************************************************** *)

type 'a existand = 'a Custom.existand = private {
  commonexistand: common;
  combineexistand: ('a,'a,'a) op2;
    (** Combining operation when a decision is eliminated *)
  bottomexistand: 'a;
    (** Value returned when intersecting with [Bdd.dfalse] *)
}
val make_existand :
  ?memo:Memo.t -> bottom:'a -> ('a, 'a, 'a) op2 -> 'a existand
val apply_existand :
  'a existand -> supp:Bdd.vt -> Bdd.vt -> 'a Vdd.t -> 'a Vdd.t

(** [existand ~bottom op2 supp bdd f] is equivalent to
    [exist op2 supp (ite bdd f bottom)].

    The leaf operation [op2:'a -> 'a -> 'a] is assumed to be
    commutative, idempotent, and also [op2 f bottom = f]. *)

(*  ********************************************************************** *)
(** {3 Quantification combined with unary operation} *)
(*  ********************************************************************** *)

type ('a,'b) existop1 = ('a,'b) Custom.existop1 = private {
  commonexistop1: common;
  combineexistop1: ('b,'b,'b) op2;
    (** Combining operation when a decision is eliminated *)
  existop1: ('a,'b) op1;
    (** Unary operations applied before elimination *)
}
val make_existop1 :
  ?memo:Memo.t -> op1:('a, 'b) op1 -> ('b, 'b, 'b) op2 -> ('a, 'b) existop1
val apply_existop1 :
  ('a, 'b) existop1 -> supp:Bdd.vt -> 'a Vdd.t -> 'b Vdd.t

(** Type of unary operation, conjunction and quantification

    [existop1 op1 op2 supp f] is equivalent to
    [exist op2 supp (op1 f)].

    The leaf operation [op2:'b -> 'b -> 'b] is assumed to be
    commutative and idempotent.
*)

(*  ********************************************************************** *)
(** {3 Quantification combined with intersection and unary operation} *)
(*  ********************************************************************** *)

type ('a,'b) existandop1 = ('a,'b) Custom.existandop1 = private {
  commonexistandop1: common;
  combineexistandop1: ('b,'b,'b) op2;
    (** Combining operation when a decision is eliminated *)
  existandop1: ('a,'b) op1;
    (** Unary operations applied before elimination *)
  bottomexistandop1: 'b;
    (** Value returned when intersecting with [Bdd.dfalse] *)
}
val make_existandop1 :
  ?memo:Memo.t ->
  op1:('a, 'b) op1 -> bottom:'b -> ('b, 'b, 'b) op2 -> ('a, 'b) existandop1
val apply_existandop1 :
  ('a, 'b) existandop1 ->supp: Bdd.vt -> Bdd.vt -> 'a Vdd.t -> 'b Vdd.t

(**
   [existandop1 ~bottom op op1 supp bdd f] is equivalent to
   [exist op2 supp (ite bdd (op1 f) bottom))].

   The leaf operation [op2:'b -> 'b -> 'b] is assumed to be
   commutative, idempotent, and also [op2 f bottom = f]. *)

(*  ********************************************************************** *)
(** {3 Clearing memoization tables} *)
(*  ********************************************************************** *)

val clear_common	: common -> unit

val clear_op1		: ('a, 'b) op1		-> unit
val clear_op2		: ('a, 'b, 'c) op2	-> unit
val clear_op3		: ('a, 'b, 'c, 'd) op3	-> unit
val clear_opN		: ('a, 'b) opN		-> unit
val clear_opG		: ('a, 'b) opG		-> unit
val clear_test2		: ('a, 'b) test2	-> unit
val clear_exist		: 'a exist		-> unit
val clear_existand	: 'a existand		-> unit
val clear_existop1	: ('a, 'b) existop1	-> unit
val clear_existandop1	: ('a, 'b) existandop1	-> unit

(*  ********************************************************************** *)
(** {3 Map operations} *)
(*  ********************************************************************** *)

(** These operations combine [make_opXXX] and [apply_opXXX]
    operations.

    if [?memo=None], then a hash table is used, and cleared at the
    end. *)

val map_op1 : ?memo:Memo.t -> ('a -> 'b) -> 'a Vdd.t -> 'b Vdd.t
val map_op2 :
  ?memo:Memo.t ->
  ?commutative:bool ->
  ?idempotent:bool ->
  ?special:('a Vdd.t -> 'b Vdd.t -> 'c Vdd.t option) ->
  ('a -> 'b -> 'c) -> 'a Vdd.t -> 'b Vdd.t -> 'c Vdd.t
val map_op3 :
  ?memo:Memo.t ->
  ?special:('a Vdd.t -> 'b Vdd.t -> 'c Vdd.t -> 'd Vdd.t option) ->
  ('a -> 'b -> 'c -> 'd) ->
  'a Vdd.t -> 'b Vdd.t -> 'c Vdd.t -> 'd Vdd.t
val map_opN :
  ?memo:Memo.t ->
  (Bdd.vt array -> 'a Vdd.t array -> 'b Vdd.t option) ->
  Bdd.vt array -> 'a Vdd.t array -> 'b Vdd.t
val map_test2 :
  ?memo:Memo.t ->
  ?symetric:bool ->
  ?reflexive:bool ->
  ?special:('a Vdd.t -> 'b Vdd.t -> bool option) ->
  ('a -> 'b -> bool) -> 'a Vdd.t -> 'b Vdd.t -> bool
