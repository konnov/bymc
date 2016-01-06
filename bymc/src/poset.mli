(**
 
  Operations on partially-ordered sets.

  We generate all linearizations of a poset using the following algorithm:

  E. Rodney Canfield, S. Gill Williamson. A loop-free algorithm for
  generating the linear extensions of a poset, 1995, Volume 12,
  Issue 1, pp 57-75.


  @author Igor Konnov, 2016
 *)


exception Poset_error of string

type po_matrix = int array array

(**
  Create a matrix representation of a (strict) partial order.

  @param n the poset's cardinality: the set \{0, ..., n-1\}
    with the partial order defined by the list pairs

  @param pairs a list of integers (a, b) meaning a < b for 0 <= a, b <= n-1

  @return an n * n array m with the following semantics:
      if m.(a).(b) = 0, then a \nprec b;
      if m.(a).(b) = 1, then a \prec b and there is no c: a \prec c \prec b;
      if m.(a).(b) = 2, then a \prec b and there is c: a \prec c \prec b.
 *)
val mk_po_matrix: int -> (int * int) list -> int array array


(**
  Check, whether a precedes b and a != b.

  @param matrix an n * n matrix
  @param a an element that is expected to be smaller
  @param b an element that is expected to be larger
  @return true iff a precedes b
 *)
val prec: po_matrix -> (* a *) int -> int -> bool

(**
  Check, whether a precedes b or a equals b.

  @param matrix an n * n matrix
  @param a an element that is expected to be smaller
  @param b an element that is expected to be larger
  @return true iff a precedes b or a equals b
 *)
val prec_eq: po_matrix -> (* a *) int -> int -> bool

