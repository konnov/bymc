(** Lifting operation on leaves to operations on MTBDDs *)

(** This module offers functions to lift operations on leaves to
    operations on MTBDDs on such leaves. Algorithmically, this is done
    by decomposing MTBDDs in lists of pairs [(guard,leaf)].

    An alternative, which may be more efficient but a bit less
    flexible, is to use functions of module {!User}.

    In order to be usable with both modules {!Mtbdd} and
    {!Mtbddc}, the signature of the functions of this modules use
    the type ['a Vdd.t], but Vdds should not be used directly. *)


(*  ********************************************************************** *)
(** {3 Global option} *)
(*  ********************************************************************** *)

val restrict : bool ref
  (** If [true], simplifies in some functions
      MTBDDs using {!Mtbdd.restrict} or {!Mtbddc.restrict}. *)

(*  ********************************************************************** *)
(** {3 Functions of arity 1} *)
(*  ********************************************************************** *)

(** In the following documentation, the pair [guard,leaf] is
    implicitly iterated on all such pairs contained in the argument
    MTBDD. *)

val mapleaf1 : ('a -> 'b) -> 'a Vdd.t -> 'b Vdd.t
  (** Return the MTBDD [\/ guard -> f leaf] *)

val retractivemapleaf1 :
  default:'a Vdd.t ->
  (Bdd.vt -> 'b -> Bdd.vt * 'a) -> 'b Vdd.t -> 'a Vdd.t
  (** Assuming that the new guards delivered by the function [f]
      are disjoint, return the MTBDD [default \/ (\/ nguard ->
      nleaf)] with [(nguard,nleaf) = f guard leaf]. *)

val expansivemapleaf1 :
  default:'a Vdd.t ->
  merge:('a Vdd.t -> 'a Vdd.t -> 'a Vdd.t) ->
  (Bdd.vt -> 'b -> Bdd.vt * 'a) -> 'b Vdd.t -> 'a Vdd.t
  (** Same as above, but with [\/] replaced by [merge] (supposed
      to be commutative and associative). *)

val combineleaf1 :
  default:'c ->
  combine:('b -> 'c -> 'c) ->
  (Bdd.vt -> 'a -> 'b) -> 'a Vdd.t -> 'c
  (** Generic function, instanciated above.  The result [acc]
      (kind of accumulator) is initialized with [default], to
      which one progressively add [combine acc (f guard leaf)].

      [combine] should not be sensitive to the order in which one
      iterates on guards and leaves.  *)

(*  ********************************************************************** *)
(** {3 Functions of arity 2} *)
(*  ********************************************************************** *)

(** In the following documentation, the pair [guard1,leaf1]
    (resp. [guard2,leaf2]) is implicitly iterated on all such
    pairs contained in the first (resp. second) argument MTBDD. *)

val mapleaf2 : ('a -> 'b -> 'c) -> 'a Vdd.t -> 'b Vdd.t -> 'c Vdd.t
  (** Return the MTBDD [\/ guard1 /\ guard2 -> f leaf1 leaf2] *)

val retractivemapleaf2 :
  default:'a Vdd.t ->
  (Bdd.vt -> 'b -> 'c -> Bdd.vt * 'a) ->
  'b Vdd.t -> 'c Vdd.t -> 'a Vdd.t
  (** Assuming that the new guards delivered by the function [f]
      are disjoint, return the MTBDD 
      [default \/ (\/ nguard -> nleaf)] with 
      [(nguard,nleaf) = f (guard1 /\ guard2) leaf1 leaf2]. *)
val expansivemapleaf2 :
  default:'a Vdd.t ->
  merge:('a Vdd.t -> 'a Vdd.t -> 'a Vdd.t) ->
  (Bdd.vt -> 'b -> 'c -> Bdd.vt * 'a) ->
  'b Vdd.t -> 'c Vdd.t -> 'a Vdd.t
  (** Same as above, but with [\/] replaced by [merge] (supposed
      to be commutative and associative). *)

val combineleaf2 :
  default:'d ->
  combine:('c -> 'd -> 'd) ->
  (Bdd.vt -> 'a -> 'b -> 'c) ->
  'a Vdd.t -> 'b Vdd.t -> 'd
  (** Generic function, instanciated above.  The result [acc]
      (kind of accumulator) is initialized with [default], to
      which one progressively add [combine acc (f (guard1 /\
      guard2) leaf1 leaf2)].

      [combine] should not be sensitive to the order in which one
      iterates on guards and leaves.  *)

(*  ********************************************************************** *)
(** {3 Functions on arrays} *)
(*  ********************************************************************** *)

(** In the following documentation, [tguard,tleaves] denotes
    resp. the conjunctions of guards (of the array of MTBDD) and
    the associated array of leaves. *)

val combineleaf_array :
  default:'c ->
  combine:('b -> 'c -> 'c) ->
  tabsorbant:('a -> bool) option array ->
  (Bdd.vt -> 'a array -> 'b) -> 'a Vdd.t array -> 'c
  (** Generic function,.  The result [acc] (kind of accumulator)
      is initialized with [default], to which one progressively
      add [combine acc (f (/\ tguard) tleaves)].  

      The arrays are assumed to be non-empty.

      If for some [i], [tabsorbant.(i)=Some abs] and [absorbant
      tleaves.(i)=true], then [f (/\ tguard) tleaves] is assumed
      to return [default] (this allows optimisation).

      [combine] should not be sensitive to the order in which one
      iterates on guards and leaves.  *)

val combineleaf1_array :
  default:'d ->
  combine:('c -> 'd -> 'd) ->
  ?absorbant:('a -> bool) ->
  tabsorbant:('b -> bool) option array ->
  (Bdd.vt -> 'a -> 'b array -> 'c) ->
  'a Vdd.t -> 'b Vdd.t array -> 'd
val combineleaf2_array :
  default:'e ->
  combine:('d -> 'e -> 'e) ->
  ?absorbant1:('a -> bool) ->
  ?absorbant2:('b -> bool) ->
  tabsorbant:('c -> bool) option array ->
  (Bdd.vt -> 'a -> 'b -> 'c array -> 'd) ->
  'a Vdd.t -> 'b Vdd.t -> 'c Vdd.t array -> 'e
  (** Functions similar to [combineleaf_array], but in which the
      first (resp. first and second) leaves (and MTBDD) type may be
      different. *)

(*  ********************************************************************** *)
(** {3 Internal functions} *)
(*  ********************************************************************** *)

val combineretractive : Bdd.vt * 'a -> 'a Vdd.t -> 'a Vdd.t
  (** [combinetractive (guard,leaf) vdd = Vdd.ite guard leaf vdd].
      Used in cases where [guard] and the guard of ``interesting
      things'' in [vdd] are disjoint, hence the name.
  *)

val combineexpansive :
  default:'a Vdd.t ->
  merge:('a Vdd.t -> 'b Vdd.t -> 'c Vdd.t) ->
  Bdd.vt * 'a -> 'b Vdd.t -> 'c Vdd.t
  (** [combineexpansive ~default ~merge (guard,leaf) vdd = merge
      (Vdd.ite guard leaf default) vdd]. Implements in some way an
      ``union'' of [(guard,leaf)] and [vdd]. *)
