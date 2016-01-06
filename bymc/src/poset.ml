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

let val_no_prec       = 0
let val_prec          = 1
let val_prec_trans    = 2


let mk_po_matrix n poset =
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


let prec mx a b =
    mx.(a).(b) > 0


let prec_eq mx a b =
    a = b || prec mx a b

