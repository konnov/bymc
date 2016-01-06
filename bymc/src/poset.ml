(**
 
  Operations on partially-ordered sets.

  We generate all linearizations of a poset using the following algorithm:

  E. Rodney Canfield, S. Gill Williamson. A loop-free algorithm for
  generating the linear extensions of a poset, 1995, Volume 12,
  Issue 1, pp 57-75.


  @author Igor Konnov, 2016
 *)

open Batteries
open BatPrintf

open Accums

exception Poset_error of string

type po_matrix = int array array

type linord_iter = {
    (** the current order, initialized with L0 in the paper*)
    m_order: int array;
    (** a precedence matrix *)
    m_matrix: po_matrix;
    (** the indices of minimal pairs (called J in the paper) *)
    m_pair_indices: int array;
}

let val_no_prec       = 0
let val_prec          = 1
let val_prec_trans    = 2


let mk_po_matrix n poset =
    if n <= 0 then raise (Poset_error "matrix size must be positive");
    let mx = Array.make_matrix n n val_no_prec in
    let check_range a =
        if a >= 0 && a < n
        then a
        else raise (Poset_error ("Element is out of range: " ^ (int_s a)))
    in
    let rec fill_matrix = function
        | [] -> ()

        | (a, b) :: tl ->
            if (check_range a) = (check_range b)
            then raise (Poset_error
                (sprintf "Anti-reflexivity violated: (%d, %d)" a a));
            if mx.(b).(a) > 0
            then raise (Poset_error
                (sprintf "Anti-symmetry violated: (%d, %d) and (%d, %d)" a b b a));
            mx.(check_range a).(check_range b) <- val_prec;
            fill_matrix tl
    in
    let rec closure (a, b) =
        let set c =
            if a <> c && b <> c && mx.(b).(c) <> val_no_prec
            then begin
                if mx.(c).(a) <> val_no_prec
                then raise (Poset_error
                    (sprintf "Anti-symmetry violated: (%d, %d) and (%d, %d)"
                        c a a c));
                mx.(a).(c) <- val_prec_trans;
                closure (a, c)
            end
        in
        if a <> b && mx.(a).(b) <> val_no_prec
        then BatEnum.iter set (0--^n)
    in
    fill_matrix poset;
    BatEnum.iter closure (BatEnum.cartesian_product (0--^n) (0--^n));
    mx


(* if you want to understand this function,
   read the paper by Canfield and Williamson, p. 70, the algorithm PC
 *)
let linord_iter_first n poset =
    (* the precedence matrix *)
    let m_matrix = mk_po_matrix n poset in
    (* the linear order as we compute it *)
    let m_order = BatArray.make n 0 in
    (* the indices of paired minimal elements *)
    let pair_indices = ref [] in
    (* an array to keep the elements in the topological order of poset *)
    let sorted = BatArray.of_enum (0--^n) in
    let cmp a b =
        let a_prec_b = m_matrix.(a).(b) <> val_no_prec
        and b_prec_a = m_matrix.(b).(a) <> val_no_prec in
        if a = b || (not a_prec_b && not b_prec_a)
        then 0
        else if a_prec_b then -1 else 1
    in
    BatArray.stable_sort cmp sorted;
    (* for each element, we record the number of the preceding elements *)
    let preceding = BatArray.make n 0 in
    let sum_cell j s i =
        if m_matrix.(i).(j) <> val_no_prec then s + 1 else s in
    let set_col j =
        preceding.(j) <- BatEnum.fold (sum_cell j) 0 (0--^n)
    in
    BatEnum.iter set_col (0--^n);
    (* the number of elements yet to be processed *)
    let nleft = ref n in
    let cross_out v =
        m_order.(n - !nleft) <- v;
        let dec j =
            if m_matrix.(v).(j) <> val_no_prec
            then preceding.(j) <- preceding.(j) - 1
        in
        BatEnum.iter dec (0--^n);
        nleft := !nleft - 1;
    in
    (* collect minimal elements, as singletons or pairs *)
    while !nleft > 0 do
        (* the first element is always minimal *)
        let a = sorted.(0) in
        assert (preceding.(a) = 0);
        (* try to find another minimal element *)
        try
            let is_minimal i = preceding.(sorted.(i)) = 0 in
            let bi = BatEnum.find is_minimal (1--^(!nleft)) in
            (* a and b are two minimal elements *)
            let b = sorted.(bi) in
            (* append pair indices *)
            let j = n - !nleft in
            pair_indices := (j + 1) :: j :: !pair_indices;
            (*printf "a = %d, b = %d, bi = %d, j = %d\n" a b bi j;*)

            (* shift sorted by one from 1 to bi - 1 *)
            if bi > 1
            then Array.blit sorted 1 sorted 0 (bi - 1);
            (* shift sorted by two from bi to the end *)
            if bi < !nleft
            then Array.blit sorted (bi + 1) sorted (bi - 1) (!nleft - (bi + 1));
            (* remove a and b and write them to m_order *)
            cross_out a; cross_out b;

        with Not_found -> begin
            (* a is the only minimal element *)
            (*printf "a = %d\n" a;*)
            Array.blit sorted 1 sorted 0 (!nleft - 1);
            cross_out a
        end
    done;
    {
        m_order; m_matrix;
        m_pair_indices = BatArray.of_list !pair_indices
    }


let linord_iter_has_next iter =
    false


let linord_iter_next iter =
    iter


let linord_iter_get iter =
    iter.m_order


let prec mx a b =
    mx.(a).(b) > 0


let prec_eq mx a b =
    a = b || prec mx a b

