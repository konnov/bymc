(** Hash tables of weak pointers, parametrized polymorphic version. *)

(** Same interface as {!Weakke}. *)

type 'a compare = 'a Weakke.compare = {
  hash : 'a -> int;
  equal : 'a -> 'a -> bool;
}

type 'a t = {
  compare : 'a compare;
  hashtbl : 'a Weakke.t
}

val create : ('a -> int) -> ('a -> 'a -> bool) -> int -> 'a t
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
