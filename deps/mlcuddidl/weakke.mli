(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Damien Doligez, projet Para, INRIA Rocquencourt          *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* $Id: weak.mli,v 1.16.2.1 2008/11/13 10:39:46 doligez Exp $ *)

(** Hash tables of weak pointers. *)

(** Original [Weak] module of OCaml distribution modified by
    Bertrand Jeannet with a [Custom] (polymorphic) module.
*)

(** A weak hash table is a hashed set of values.  Each value may
    magically disappear from the set when it is not used by the
    rest of the program any more.  This is normally used to share
    data structures without inducing memory leaks.
    Weak hash tables are defined on values from a {!Hashtbl.HashedType}
    module; the [equal] relation and [hash] function are taken from that
    module.  We will say that [v] is an instance of [x] if [equal x v]
    is [true].

    The [equal] relation must be able to work on a shallow copy of
    the values and give the same result as with the values themselves.
*)

type 'a t
type 'a hashtbl = 'a t
type 'a compare = { hash : 'a -> int; equal : 'a -> 'a -> bool; }

val create : int -> 'a t
val clear : 'a t -> unit
val merge : 'a t -> 'a -> 'a
val merge_map : 'a t -> 'a -> ('a -> 'a) -> 'a
val add : 'a t -> 'a -> unit
val remove : 'a t -> 'a -> unit
val find : 'a t -> 'a -> 'a
val find_all : 'a t -> 'a -> 'a list
val mem : 'a t -> 'a -> bool
val iter : ('a -> 'b) -> 'a t -> unit
val fold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
val count : 'a t -> int
val stats : 'a t -> int * int * int * int * int * int
val print :
  ?first:(unit, Format.formatter, unit) format ->
  ?sep:(unit, Format.formatter, unit) format ->
  ?last:(unit, Format.formatter, unit) format ->
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a t -> unit

module type S = sig
  type data
    (** The type of the elements stored in the table. *)
  type t
    (** The type of tables that contain elements of type [data].
	Note that weak hash tables cannot be marshaled using
	{!Pervasives.output_value} or the functions of the {!Marshal}
	module. *)
  val create : int -> t
    (** [create n] creates a new empty weak hash table, of initial
	size [n].  The table will grow as needed. *)
  val clear : t -> unit
    (** Remove all elements from the table. *)
  val merge : t -> data -> data
    (** [merge t x] returns an instance of [x] found in [t] if any,
	or else adds [x] to [t] and return [x]. *)
  val merge_map : t -> data -> (data -> data) -> data
    (** Variant of [merge]: [merge_map t x f] is equivalent to
	[try find t x with Not_found -> let y = f x in add t y; Some y].
	bE CAUTIOUS: [f x] is assumed to be equal to [x].
    *)
  val add : t -> data -> unit
    (** [add t x] adds [x] to [t].  If there is already an instance
	of [x] in [t], it is unspecified which one will be
	returned by subsequent calls to [find] and [merge]. *)
  val remove : t -> data -> unit
    (** [remove t x] removes from [t] one instance of [x].  Does
	nothing if there is no instance of [x] in [t]. *)
  val find : t -> data -> data
    (** [find t x] returns an instance of [x] found in [t].
	Raise [Not_found] if there is no such element. *)
  val find_all : t -> data -> data list
    (** [find_all t x] returns a list of all the instances of [x]
	found in [t]. *)
  val mem : t -> data -> bool
    (** [mem t x] returns [true] if there is at least one instance
	of [x] in [t], false otherwise. *)
  val iter : (data -> unit) -> t -> unit
    (** [iter f t] calls [f] on each element of [t], in some unspecified
	order.  It is not specified what happens if [f] tries to change
	[t] itself. *)
  val fold : (data -> 'a -> 'a) -> t -> 'a -> 'a
    (** [fold f t init] computes [(f d1 (... (f dN init)))] where
	[d1 ... dN] are the elements of [t] in some unspecified order.
	It is not specified what happens if [f] tries to change [t]
	itself. *)
  val count : t -> int
    (** Count the number of elements in the table.  [count t] gives the
	same result as [fold (fun _ n -> n+1) t 0] but does not delay the
	deallocation of the dead elements. *)
  val stats : t -> int * int * int * int * int * int
    (** Return statistics on the table.  The numbers are, in order:
	table length, number of entries, sum of bucket lengths,
	smallest bucket length, median bucket length, biggest bucket length. *)
  val print :
    ?first:(unit, Format.formatter, unit) format ->
    ?sep:(unit, Format.formatter, unit) format ->
    ?last:(unit, Format.formatter, unit) format ->
    (Format.formatter -> data -> unit) ->
    Format.formatter -> t -> unit
    (** Printing function *)
end;;
(** The output signature of the functor {!Weak.Make}. *)

module Make (H : Hashtbl.HashedType) : S with type data = H.t;;
(** Functor building an implementation of the weak hash table structure. *)

module Compare : sig
  val add : 'a compare -> 'a t -> 'a -> unit
  val find_or : 'a compare -> 'a t -> 'a -> (int -> int -> 'a) -> 'a
  val merge : 'a compare -> 'a t -> 'a -> 'a
  val merge_map : 'a compare -> 'a t -> 'a -> ('a -> 'a) -> 'a
  val find : 'a compare -> 'a t -> 'a -> 'a
  val find_shadow :
    'a compare -> 'a t -> 'a -> ('a Weak.t -> int -> 'b) -> 'b -> 'b
  val remove : 'a compare -> 'a t -> 'a -> unit
  val mem : 'a compare -> 'a t -> 'a -> bool
  val find_all : 'a compare -> 'a t -> 'a -> 'a list
end
