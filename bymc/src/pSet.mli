(*
  Set membership as division by prime numbers.
  This was a clever exercise. However, it is much easier
  (and probably more efficient) to use a bit vector instead of prime
  numbers.

  Igor Konnov, 2014
 *)

type elt
type t

(* this is supposed to work with very small prime numbers *)
val new_thing: unit -> elt

val str: t -> string

val empty: t

val singleton: elt -> t

val is_empty: t -> bool

val mem: elt -> t -> bool

val add: elt -> t -> t

val remove: elt -> t -> t

val compare: t -> t -> int

val compare_elt: elt -> elt -> int

val inter: t -> t -> t

val union: t -> t -> t

val diff: t -> t -> t

val equal: t -> t -> bool

val subseteq: t -> t -> bool

