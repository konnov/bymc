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

module G = Graph.Pack.Digraph
module Topo = Graph.Topological.Make_stable(G)


exception Poset_error of string

type po_matrix_t = int array array

type sign_t = POS | NEG

let sign_s s = if s = POS then "+" else "-"

(* the infinity value for linord_iter_t.m_p *)
let infty = -8      (* for m_p, any negative number will do the job *)


type linord_iter_t = {
    (* the poset cardinality *)
    m_size: int;
    (** an array of signs, called S_i in the paper *)
    m_signs: sign_t array;
    (** an array of epsilon signs, called \eps_i in the paper *)
    m_epss: sign_t array;
    (** the current order, initialized with L0 in the paper*)
    m_order: int array;
    (** a precedence matrix *)
    m_matrix: po_matrix_t;
    (** the indices of minimal pairs (called J in the paper, even length) *)
    m_J: int array;
    (** the length of m_pair_indices / 2, called k in the paper *)
    m_npairs: int;
    (** the current value of the indices from m_J *)
    m_I: int array;
    (** an array controling the enumeration, called v in the paper *)
    m_v: bool array;
    (** an efficient representation of m_v (see p. 62 in the paper).
        To implement p as in the paper, we use the indices from 1 to k + 1,
        so index 0 is never updated.
     *)
    m_p: int array;
    (** a flag indicating, whether we have reached the end *)
    m_halt: bool ref;
}

let val_no_prec       = 0
let val_prec          = 1
let val_prec_trans    = 2


let mk_po_matrix n poset =
    if n <= 0 then raise (Poset_error "matrix size must be positive");
    let mx = Array.make_matrix n n val_no_prec in
    (* the precedence matrix *)
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
    let prow i =
        let pp j = sprintf "%2d" mx.(i).(j) in
        printf "  %s\n" (str_join " " (List.map pp (range 0 n)))
    in
    Debug.ltrace Trc.pos (lazy (printf "matrix:\n"; List.iter prow (range 0 n); "------\n"));
    mx


let prec mx a b =
    mx.(a).(b) > 0


let prec_eq mx a b =
    a = b || prec mx a b


(** Create a linear extension of a poset with equal elements
    sorted in the natural order. Use a stable topological sort for that.
 *)
let mk_sorted_linorder n poset =
    let pp (a, b) = sprintf "(%d, %d)" a b in
    Debug.ltrace Trc.pos
        (lazy (sprintf "poset = [%s]\n"
            (Accums.str_join ", " (List.map pp poset))));
    let vertices = Hashtbl.create n in
    let g = G.create () in
    let mkv i =
        try Hashtbl.find vertices i
        with Not_found ->
            let v = G.V.create i in
            G.add_vertex g v;
            Hashtbl.add vertices i v; v
    in
    BatEnum.iter (fun i -> ignore (mkv i)) (0--^n);
    let add_edge (a, b) =
        G.add_edge g (mkv a) (mkv b)
    in
    List.iter add_edge poset;
    let sorted = BatArray.of_enum (0--^n) in
    let set v i =
        sorted.(i) <- G.V.label v;
        i + 1
    in
    ignore (Topo.fold set g 0);
    (* an array to keep the elements in the topological order of poset *)
    sorted


(* if you want to understand this function,
   read the paper by Canfield and Williamson, p. 70, the algorithm PC
 *)
let linord_iter_first n poset =
    let m_matrix = mk_po_matrix n poset in
    (* the linear order as we compute it *)
    let m_order = BatArray.make n 0 in
    (* the indices of paired minimal elements *)
    let pair_indices = ref [] in
    (* an array to keep the elements in the topological order of poset *)
    let sorted = mk_sorted_linorder n poset in
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
    (* append an element to the order, remove from the set *)
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
        Debug.ltrace Trc.pos
            (lazy (sprintf "sorted = %s\n"
                (str_join ", " (List.map int_s (Array.to_list sorted)))));
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
            Debug.ltrace Trc.pos
                (lazy (sprintf "a pair: a = %d, b = %d, bi = %d, j = %d\n" a b bi j));

            (* TODO: do it w/o shifting, just by setting preceding to -1 *)
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
            Debug.ltrace Trc.pos (lazy (sprintf "a singleton: a = %d\n" a));
            Array.blit sorted 1 sorted 0 (!nleft - 1);
            cross_out a
        end
    done;
    let js = BatArray.of_list (List.rev !pair_indices) in
    let npairs = (BatArray.length js) / 2 in
    assert ((BatArray.length js) mod 2 = 0);
    {
        m_size = n;
        m_signs = BatArray.make (npairs + 1) POS;
        m_epss = BatArray.make npairs POS;
        m_order; m_matrix;
        m_J = js; m_I = BatArray.copy js;
        m_npairs = npairs;
        m_v = BatArray.make (npairs + 1) true;
        m_p = BatArray.make (npairs + 2) 0;
        m_halt = ref false;
    }


type move_result_t =
    | NO_MOVE | FLIP_SIGN
    | RIGHT_SWAP_A | RIGHT_SWAP_B | LEFT_SWAP_A | LEFT_SWAP_B

let move_result_s = function
    | NO_MOVE       -> "NO_MOVE"
    | FLIP_SIGN     -> "FLIP_SIGN"
    | RIGHT_SWAP_A  -> "RIGHT_SWAP_A"
    | RIGHT_SWAP_B  -> "RIGHT_SWAP_B"
    | LEFT_SWAP_A   -> "LEFT_SWAP_A"
    | LEFT_SWAP_B   -> "LEFT_SWAP_B"


(*
  Next move as explained in Theorem 3 (p. 67).
  If you really want to understand what is going on here,
  then read the paper by Canfield and Williamson.

  The only difference is that we pass the array directly and its offset.
 *)
let next_move offs sign iter i j =
    let pos p = p + offs            (* the position within the suffix *)
    in
    let i1, i2 = min i j, max i j in
    if i2 = pos 1 (* I2 = 2 in Thm. 3: a and b are in the leftmost positions *)
    then begin
        (* Case 1 of Thm. 3 (NEXT MOVE) *)
        (* i2 = 1 implies i1 = 0 *)
        Debug.trace Trc.pos (fun _ -> sprintf "  case 1\n");
        if sign = NEG
        then NO_MOVE (* the end of the canonical path *)
        else begin
            (* switch b with its right neighbor, if possible *)
            let b = iter.m_order.(i2) in
            if i2 + 1 < iter.m_size
                && not (prec iter.m_matrix b iter.m_order.(i2 + 1))
            then RIGHT_SWAP_B
            else begin
                if not (i2 + 1 < iter.m_size)
                then Debug.trace Trc.pos
                    (fun _ -> sprintf "    b is in the rightmost position\n")
                else Debug.trace Trc.pos
                    (fun _ -> sprintf "    b = %d < %d\n" b iter.m_order.(i2 + 1));
                FLIP_SIGN (* jumping to the express lane *)
            end
        end
    end
    else if i2 > (pos 1) && i1 = (pos 0) && sign = NEG
    (* Case 2 (NEXT MOVE): I2 > 2, I1 = 1, S = - => the express lane *)
    then begin
        Debug.trace Trc.pos (fun _ -> sprintf "  case 2\n");
        LEFT_SWAP_B
    end else begin
    (* Case 3 (NEXT MOVE) *)
        Debug.trace Trc.pos (fun _ -> sprintf "  case 3\n");
        let a = iter.m_order.(i1) in
        let is_i2_odd = (i2 - offs + 1) mod 2 <> 0 in (* mind the offset *)
        match (is_i2_odd, sign) with
        | (true,  POS) -> (* odd+ *)
            (* a is moving right *)
            if i1 + 1 >= i2 (* do not swap a and b, i.e., pos(a) < pos(b) *)
            then begin
                Debug.trace Trc.pos (fun _ -> sprintf "    a is next to b\n");
                FLIP_SIGN
            end else if prec iter.m_matrix a iter.m_order.(i1 + 1)
            then begin (* a cannot be moved to the right *)
                Debug.trace Trc.pos
                    (fun _ -> sprintf "    a = %d < %d\n" a iter.m_order.(i1 + 1));
                if i1 = pos 0 && i2 + 1 < iter.m_size
                then begin
                    (* If we flip the sign right here, we will jump on the express lane
                       and miss all the cases when b moves to the right. So, try to
                       push b to the right first. *)
                    Debug.trace Trc.pos
                        (fun _ -> "    check, whether b can be pushed to the right\n");
                    let b = iter.m_order.(i2) in
                    if not (prec iter.m_matrix b iter.m_order.(i2 + 1))
                    then RIGHT_SWAP_B
                    else begin
                        Debug.trace Trc.pos
                            (fun _ -> sprintf "    b = %d < %d\n" b iter.m_order.(i2 + 1));
                        FLIP_SIGN
                    end
                end
                else FLIP_SIGN (* a will be moved to the left *)
            end
            else RIGHT_SWAP_A

        | (true,  NEG) -> (* odd- *)
            (* a is moving left *)
            if i1 - 1 >= pos 1 (* mind the express lane *)
                && not (prec iter.m_matrix iter.m_order.(i1 - 1) a)
            then LEFT_SWAP_A
            else begin
                (* try move upwards, i.e., b moves right *)
                let b = iter.m_order.(i2) in
                if i2 + 1 < iter.m_size
                    && not (prec iter.m_matrix b iter.m_order.(i2 + 1))
                then RIGHT_SWAP_B   (* move upwards: b moves right *)
                else begin
                    Debug.trace Trc.pos (fun _ -> sprintf "    EXPRESS LANE!\n");
                    LEFT_SWAP_A    (* switch to the express lane *)
                end
            end

        | (false, POS) -> (* even+ *)
            (* a is moving left *)
            if i1 - 1 >= pos 0
                && not (prec iter.m_matrix iter.m_order.(i1 - 1) a)
            then LEFT_SWAP_A
            else begin
                (* try move upwards, i.e., b moves right *)
                let b = iter.m_order.(i2) in
                if i2 + 1 < iter.m_size
                    && not (prec iter.m_matrix b iter.m_order.(i2 + 1))
                then RIGHT_SWAP_B   (* move upwards: b moves right *)
                else begin
                    Debug.trace Trc.pos (fun _ -> sprintf "    EXPRESS LANE!\n");
                    FLIP_SIGN      (* switch to the express lane *)
                end
            end

        | (false, NEG) -> (* even- *)
            (* a is moving right *)
            if i1 + 1 >= i2 (* do not swap a and b, i.e., pos(a) < pos(b) *)
            then begin
                Debug.trace Trc.pos (fun _ -> sprintf "    a is next to b\n");
                FLIP_SIGN
            end else if prec iter.m_matrix a iter.m_order.(i1 + 1)
            then begin (* a cannot be moved to the right *)
                Debug.trace Trc.pos
                    (fun _ -> sprintf "    a = %d < %d\n" a iter.m_order.(i1 + 1));
                FLIP_SIGN
            end
            else RIGHT_SWAP_A
    end


(*
  Reverse the next move as explained in Theorem 3 (p. 67).
  If you really want to understand what is going on here,
  then read the paper by Canfield and Williamson.
 *)
let prev_move offs sign iter i j =
    let pos p = p + offs            (* the position within the suffix *)
    in
    let i1, i2 = min i j, max i j in
    if i2 = pos 1 (* I2 = 2 in Thm. 3 *)
    then begin
    (* Case 1 of Thm. 3 (PREV MOVE): a and b are in the leftmost positions *)
        if sign = POS
        then NO_MOVE (* the end of the anti-canonical path *)
        else begin
            (* switch b with its right neighbor, if possible *)
            let b = iter.m_order.(i2) in
            if i2 + 1 < iter.m_size
                && not (prec iter.m_matrix b iter.m_order.(i2 + 1))
            then RIGHT_SWAP_B
            else begin
                if not (i2 + 1 < iter.m_size)
                then Debug.trace Trc.pos
                    (fun _ -> "    b is in the rightmost position\n")
                else Debug.trace Trc.pos
                    (fun _ -> sprintf "    b = %d < %d\n" b iter.m_order.(i2 + 1));
                FLIP_SIGN (* jumping to the leftmost position *)
            end
        end
    end
    else if i2 > (pos 1) && i1 = (pos 0) && sign = NEG
    (* Case 2 (PREV MOVE): I2 > 2, I1 = 1, S = - => the express lane *)
    then begin
        let a = iter.m_order.(i1) in
        let b = iter.m_order.(i2) in
        let is_even =
            (i2 + 1 - offs) mod 2 = 0 (* the original paper counts indices from 1 *) in
        let jump_off =
            i2 + 1 >= iter.m_size || (prec iter.m_matrix b iter.m_order.(i2 + 1))
        in
        if not jump_off
        then RIGHT_SWAP_B (* move upwards the express lane *)
        else if is_even
            then begin
                Debug.trace Trc.pos
                    (fun _ -> "    OFF THE EXPRESS LANE (EVEN)!\n");
                FLIP_SIGN      (* jump off the express lane in the odd case*)
            end
            else begin
                (* we should move a to the right, but only if we allowed to *)
                Debug.trace Trc.pos (fun _ -> "    OFF THE EXPRESS LANE (ODD)!\n");
                if i1 + 1 < i2 && not (prec iter.m_matrix a iter.m_order.(i1 + 1))
                then RIGHT_SWAP_A
                else FLIP_SIGN
            end
    end else begin
    (* Case 3 (PREV MOVE) *)
        let a = iter.m_order.(i1) in
        let b = iter.m_order.(i2) in
        let is_i2_odd = (i2 - offs + 1) mod 2 <> 0 in (* mind the offset *)
        match (is_i2_odd, sign) with
        | (true,  POS) (* antipath: odd+ *)->
            (* a is moving left *)
            if i1 - 1 >= pos 0
                && not (prec iter.m_matrix iter.m_order.(i1 - 1) a) 
            then LEFT_SWAP_A
            else begin
                (* try move downwards, i.e., b moves left *)
                if i2 - 1 > i1
                    && not (prec iter.m_matrix iter.m_order.(i2 - 1) b)
                then LEFT_SWAP_B   (* move downwards: b moves left *)
                else assert(false) (* XXX: looks like an impossible case *)
            end

        | (true,  NEG) (* antipath: odd- *) ->
            (* a is moving right *)
            if i1 + 1 < i2 (* do not swap a and b *)
                && not (prec iter.m_matrix a iter.m_order.(i1 + 1))
            then RIGHT_SWAP_A
            else begin
                if not (i1 + 1 < iter.m_size)
                then Debug.trace Trc.pos
                    (fun _ -> "    a is in the rightmost position\n")
                else Debug.trace Trc.pos
                    (fun _ -> sprintf "    a = %d < %d\n" a iter.m_order.(i1 + 1));
                FLIP_SIGN
            end

        | (false, POS) (* antipath: even+ *) ->
            (* a is moving right *)
            if i1 + 1 < i2 (* do not swap a and b *)
                && not (prec iter.m_matrix a iter.m_order.(i1 + 1))
                && i1 + 1 <> i2 (* do not swap a and b *)
                (*&& i1 + 1 <> iter.m_size - 1 (* no express lane yet *) *)
            then RIGHT_SWAP_A
            else begin
                if i1 + 1 >= i2
                then Debug.trace Trc.pos
                    (fun _ -> "    a is next to b\n")
                else Debug.trace Trc.pos
                    (fun _ -> sprintf "    a = %d < %d\n" a iter.m_order.(i1 + 1));

                if i1 <> pos 0 && i2 < iter.m_size
                then FLIP_SIGN (* from + to - *)
                else (* If we flip the sign, then we are back on the express lane.
                        Try move downwards, i.e., b moves left. *)
                    if i2 - 1 >= pos 0
                        && not (prec iter.m_matrix iter.m_order.(i2 - 1) b)
                        && i1 < i2 - 1 (* do not swap a and b *)
                    then LEFT_SWAP_B
                    else assert(false);
            end


        | (false, NEG) (* antipath: even- *) ->
            (* a is moving left *)
            if i1 - 1 >= pos 1 (* do not jump on the express lane! *)
                && not (prec iter.m_matrix iter.m_order.(i1 - 1) a) 
            then LEFT_SWAP_A
            else begin
                (* try move downwards, i.e., b moves left *)
                let b = iter.m_order.(i2) in
                if i2 - 1 > i1
                    && not (prec iter.m_matrix iter.m_order.(i2 - 1) b)
                then LEFT_SWAP_B   (* move downwards: b moves left *)
                else assert(false) (* XXX: looks like an impossible case *)
            end
    end


let next_or_prev_move offs eps sign iter i j =
    if eps = POS
    then next_move offs sign iter i j
    else prev_move offs sign iter i j


let bool_s b = if b then "1" else "0"


(* One iteration of the algorithm NRPR (a version with loops inside).
   I have implemented it for debugging purposes, as this version is
   much easier to understand and debug, as opposed to GLPPR,
   which is implemented in linord_iter_next.

   Anyways, if you want to understand what is going, read the paper. *)
let linord_iter_next_signed_w_loops iter =
    let getJ t = (* like J_t in the algorithm *)
        iter.m_J.(t)
    in
    let getJ_i i = getJ (2 * i) in
    let getI t = (* like I_j in the algorithm *)
        iter.m_I.(t)
    in
    let setI t v = (* like I_j in the algorithm *)
        iter.m_I.(t) <- v
    in
    let getS i = iter.m_signs.(i) in
    let getEps i = iter.m_epss.(i) in
    let swap i j =
        let t = iter.m_order.(i) in
        iter.m_order.(i) <- iter.m_order.(j);
        iter.m_order.(j) <- t
    in
    if !(iter.m_halt)
    then () (* already beyond the last element *)
    else if iter.m_npairs = 0
    (* the only order was created with linord_iter_first *)
    then iter.m_halt := true
    else
        let i = ref 0 (* always start with 0 *) in
        let k = iter.m_npairs in
        let seq_s pos n =
            if pos = 2 * !i || pos = 2 * !i + 1
            then sprintf "%d+" n
            else sprintf "%d" n
        in
        Debug.trace Trc.pos (fun _ ->
            sprintf "i = %d, k = %d, eps = [%s], S = [%s], L=[%s]\n"
                !i k
                (str_join "," (List.map sign_s (BatArray.to_list iter.m_epss)))
                (str_join "," (List.map sign_s (BatArray.to_list iter.m_signs)))
                (str_join "" (List.map2 seq_s (range 0 iter.m_size) (BatArray.to_list iter.m_order)))
        );
        (* make the move *)
        let print_state _ =
            Debug.trace Trc.pos (fun _ ->
                sprintf "  eps = %s, S = %s, I = [%s], J = [%s], ji = %d\n"
                    (if (getEps !i) = POS then "+" else "-")
                    (if (getS !i) = POS then "+" else "-")
                    (str_join ", " (List.map2 seq_s (range 0 (2 * k)) (BatArray.to_list iter.m_I)))
                    (str_join ", " (List.map int_s (BatArray.to_list iter.m_J)))
                    (getJ !i))
        in
        let print_move m =
            Debug.trace Trc.pos (fun _ -> sprintf "  move: %s\n" (move_result_s m))
        in
        let move = ref NO_MOVE in
        while !move = NO_MOVE && !i < k do
            print_state ();
            move := next_or_prev_move (getJ_i !i) (getEps !i) (getS !i)
                    iter (getI (2 * !i)) (getI (2 * !i + 1));
            print_move !move;
            if !move = NO_MOVE
            then begin
                iter.m_epss.(!i) <- (if getEps !i = POS then NEG else POS);
                i := !i + 1;
            end
        done;

        if !i = k (* line 3a *)
        then begin
            if (getS k) = NEG
            then iter.m_halt := true
            else begin
                swap (getI (2 * k - 2)) (getI (2 * k - 1));
                iter.m_signs.(k) <-
                    (if iter.m_signs.(k) = POS then NEG else POS);
            end;

            Debug.trace Trc.pos (fun _ ->
                sprintf "  => SWAP %d and %d\n  => [%s]\n"
                    (getI (2 * k - 2)) (getI (2 * k - 1))
                    (str_join ", " (BatArray.to_list (BatArray.map int_s iter.m_order))));
        end else begin
            let i1, i2 = getI (2 * !i), getI (2 * !i + 1) in
            begin
                (* line 4f *)
                match !move with
                | FLIP_SIGN ->
                    (* line 4g *)
                    iter.m_signs.(!i) <-
                        (if iter.m_signs.(!i) = POS then NEG else POS);
                    if !i > 0
                    then swap (getI (2 * !i - 2)) (getI (2 * !i - 1))

                | RIGHT_SWAP_A ->
                    (* line 4h *)
                    swap i1 (i1 + 1);
                    setI (2 * !i) (i1 + 1)

                | RIGHT_SWAP_B ->
                    (* line 4h *)
                    swap i2 (i2 + 1);
                    setI (2 * !i + 1) (i2 + 1)

                | LEFT_SWAP_A ->
                    (* line 4h *)
                    swap i1 (i1 - 1);
                    setI (2 * !i) (i1 - 1)

                | LEFT_SWAP_B ->
                    (* line 4h *)
                    swap i2 (i2 - 1);
                    setI (2 * !i + 1) (i2 - 1)

                | NO_MOVE ->
                    (* this case should never happen in the algorithm *)
                    printf "  NO MOVE\n";
                    assert(false);
            end;
            (* line 6 *)
            BatEnum.iter (fun j -> iter.m_v.(j) <- true) (0--^(!i));
            Debug.trace Trc.pos (fun _ ->
                sprintf "  => [%s]\n"
                    (str_join ", " (BatArray.to_list (BatArray.map int_s iter.m_order)))
            );
        end


(*
   One iteration of the algorithm GLPPR (as in the paper).
   In our experiments, its running time is comparable
   to linord_iter_next_signed_w_loops. As the latter is much easier to understand,
   we will perhaps switch to it in the future.
 *)
let linord_iter_next_signed iter =
    let getJ i = (* like J_t in the algorithm *)
        iter.m_J.(i)
    in
    let getI i = (* like I_j in the algorithm *)
        iter.m_I.(i)
    in
    let setI i v = (* like I_j in the algorithm *)
        iter.m_I.(i) <- v
    in
    let set_v_to_false j =
        let j1 = j + 1 in
        if j1 = iter.m_npairs + 1
        then iter.m_p.(j1) <- infty
        else if iter.m_p.(j1 + 1) = 0
            then iter.m_p.(j1) <- j1 + 1
            else begin (* iter.m_p.(i + 1) <> infty *)
                iter.m_p.(j1) <- iter.m_p.(j1 + 1);
                iter.m_p.(j1 + 1) <- 0
            end;
        (*printf "set_v_to_false %d results in: %s\n" j
            (str_join "," (List.map int_s (BatArray.to_list iter.m_p)));*)
    in
    let set_v_to_true j =
        iter.m_p.(j + 1) <- 0; (* 0-based to 1-based *)
        (*printf "set_v_to_true %d results in: %s\n" j
            (str_join "," (List.map int_s (BatArray.to_list iter.m_p)));*)
    in
    let set_smaller_vs_to_true j =
        if j > 0                (* if j = 0, do not reset anything *)
        then iter.m_p.(1) <- 0; (* set v[j] to true for j < i *)
        (*printf "set_smaller_vs_to_true %d results in: %s\n" j
            (str_join "," (List.map int_s (BatArray.to_list iter.m_p)));*)
    in
    let find_min_v_true _ =
        let v = iter.m_p.(1) in
        let res =
            if v = infty
            then infty      (* there is no i s.t. v[i] = true *)
            else if v = 0
                then 0      (* index 0 *)
                else v - 1  (* the minimum such i that v[i] = true *)
        in
        (*printf "find_min_v_true on %s results in %d\n"
            (str_join "," (List.map int_s (BatArray.to_list iter.m_p))) res;*)
        res
    in
    let swap i j =
        let t = iter.m_order.(i) in
        iter.m_order.(i) <- iter.m_order.(j);
        iter.m_order.(j) <- t
    in
    let flip_eps i =
        let j1, j2 = getJ (2 * i), getJ (2 * i + 1) in
        let i1, i2 = getI (2 * i), getI (2 * i + 1) in
        (* line 5: L(I_{i1}) and L(I_{i2}) came to the end of their circuit *)
        let eps = iter.m_epss.(i) and s = iter.m_signs.(i) in
        if (eps = POS && s = NEG || eps = NEG && s = POS) && i1 = j1 && i2 = j2
        then begin
            Debug.trace Trc.pos
                (fun _ -> sprintf "  flip eps_%d, v[%d] <- false\n" i i);
            iter.m_epss.(i) <- if eps = POS then NEG else POS;

            (* iter.m_v.(i) <- false; *)
            (* use the p-representation, see Theorem 2 *)
            set_v_to_false i
        end else begin
            Debug.trace Trc.pos (fun _ -> sprintf "  v[%d] <- true\n" i);
            (*iter.m_v.(i) <- true;*) (* redundant? *)
            set_v_to_true i
        end
    in
    if !(iter.m_halt)
    then () (* already beyond the last element *)
    else if iter.m_npairs = 0
    (* the only order was created with linord_iter_first *)
    then iter.m_halt := true
    else
        (* line 3 *)
        (* use the p-representation instead (see Theorem 2) *)
        let i = find_min_v_true () in
        (* let i = BatArray.findi (fun b -> b) iter.m_v in *)
        if i = infty
        then begin
            (* line 2: the end *)
            Debug.trace Trc.pos (fun _ -> sprintf "  => HALT\n");
            flush stdout;
            iter.m_halt := true
        end else begin
            (* compute the next linear order *)
            let seq_s pos n =
                if pos = 2 * i || pos = 2 * i + 1
                then sprintf "%d+" n
                else sprintf "%d" n
            in
            let k = iter.m_npairs in
            Debug.trace Trc.pos (fun _ ->
                sprintf "i = %d, k = %d, p = [%s], eps = [%s], S = [%s], L=[%s]\n"
                    i k (str_join "," (List.map int_s (BatArray.to_list iter.m_p)))
                    (str_join "," (List.map sign_s (BatArray.to_list iter.m_epss)))
                    (str_join "," (List.map sign_s (BatArray.to_list iter.m_signs)))
                    (str_join "" (List.map2 seq_s (range 0 iter.m_size) (BatArray.to_list iter.m_order)))
            );
            if i = k (* line 4a *)
            then begin
                (* line 4d *)
                (*iter.m_v.(k) <- false;*)
                set_v_to_false k;
                (* line 4b *)
                swap (getI (2 * k - 2)) (getI (2 * k - 1));
                (* line 4c *)
                (* this value is never used *)
                iter.m_signs.(k) <- NEG; (* S_i starts with 0, so add one *)
                (* line 6 *)
                (* BatEnum.iter (fun j -> iter.m_v.(j) <- true) (0--^i); *)
                (* use the p-representation instead *)
                set_smaller_vs_to_true k;
                Debug.trace Trc.pos (fun _ ->
                    sprintf "  => [%s]\n"
                        (str_join ", " (BatArray.to_list (BatArray.map int_s iter.m_order))));
            end else begin
                let i1, i2 = getI (2 * i), getI (2 * i + 1) in
                let ji = getJ (2 * i) in
                let s = iter.m_signs.(i) in
                let eps = iter.m_epss.(i) in
                Debug.trace Trc.pos (fun _ ->
                    sprintf "  eps = %s, S = %s, I = [%s], J = [%s], ji = %d\n"
                        (if eps = POS then "+" else "-")
                        (if s = POS then "+" else "-")
                        (str_join ", " (List.map2 seq_s (range 0 (2 * k)) (BatArray.to_list iter.m_I)))
                        (str_join ", " (List.map int_s (BatArray.to_list iter.m_J)))
                        ji);
                begin
                    (* line 4f *)
                    match next_or_prev_move ji eps s iter i1 i2 with
                    | FLIP_SIGN ->
                        Debug.trace Trc.pos (fun _ -> sprintf "  flip sign\n");
                        (* line 4g *)
                        iter.m_signs.(i) <- (* +1 *)
                            (if iter.m_signs.(i) = POS then NEG else POS);
                        if i > 0
                        then swap (getI (2 * i - 2)) (getI (2 * i - 1));
                        (* Canfield and Williamson missed
                           this simple case in their paper: *)
                        flip_eps i

                    | RIGHT_SWAP_A ->
                        Debug.trace Trc.pos (fun _ -> sprintf "  right swap a\n");
                        (* line 4h *)
                        swap i1 (i1 + 1);
                        setI (2 * i) (i1 + 1);
                        flip_eps i

                    | RIGHT_SWAP_B ->
                        Debug.trace Trc.pos (fun _ -> sprintf "  right swap b\n");
                        (* line 4h *)
                        swap i2 (i2 + 1);
                        setI (2 * i + 1) (i2 + 1);
                        flip_eps i

                    | LEFT_SWAP_A ->
                        Debug.trace Trc.pos (fun _ -> sprintf "  left swap a\n");
                        (* line 4h *)
                        swap i1 (i1 - 1);
                        setI (2 * i) (i1 - 1);
                        flip_eps i

                    | LEFT_SWAP_B ->
                        Debug.trace Trc.pos (fun _ -> sprintf "  left swap b\n");
                        (* line 4h *)
                        swap i2 (i2 - 1);
                        setI (2 * i + 1) (i2 - 1);
                        flip_eps i

                    | NO_MOVE ->
                        (* this case should never happen in the algorithm *)
                        printf "  NO MOVE\n";
                        assert(false);
                end;
                (* line 6 *)
                (* BatEnum.iter (fun j -> iter.m_v.(j) <- true) (0--^i); *)
                (* use the p-representation instead (see Theorem 2) *)
                set_smaller_vs_to_true i;

                Debug.trace Trc.pos (fun _ ->
                    sprintf "  => [%s]\n"
                        (str_join ", " (BatArray.to_list (BatArray.map int_s iter.m_order)))
                );
            end
        end


(* As explained in the paper, we leave only the orders with
   the positive master sign (S_0).
 *)
let linord_iter_next iter =
    flush stdout;
    if not !(iter.m_halt)
    then begin 

        linord_iter_next_signed iter;
        while not !(iter.m_halt) && iter.m_signs.(0) = NEG do
            linord_iter_next_signed iter;
        done

        (* if you want to debug next_move and prev_move,
           comment out the previous four lines and uncomment
           the following code, which is much easier to follow:
         *)
        (*
        linord_iter_next_signed_w_loops iter;
        while not !(iter.m_halt) && iter.m_signs.(0) = NEG do
            linord_iter_next_signed_w_loops iter;
        done
        *)
    end


let linord_iter_is_end iter =
    !(iter.m_halt)


let linord_iter_get iter =
    if !(iter.m_halt)
    then raise (Poset_error "The end of the sequence has been reached")
    else iter.m_order


let linord_iter_get_matrix iter =
    iter.m_matrix

