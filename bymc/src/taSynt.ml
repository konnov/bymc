(**
  Synthesizing threshold automata using CEGYS.

  @author Igor Konnov, 2016
 *)

open Batteries

open Printf

open Accums
open Spin
open SpinIr
open SymbSkel
open SchemaSmt


exception No_solution


module BI = BatBig_int

(** an iterator over the vectors of unknowns a_1, ..., a_k *)
type vec_iter_t = {
    (** the names of the unknowns *)
    f_names: string list;
    (** the degree of the upper bound (2^f_degree) on the unknowns' values *)
    f_degree: int;
    (** an integer that encodes the signs (s_i) and the values (each value v_i
        is represented with a bit string v^1_i, ..., v^m_i) as follows:
        v^1_1, ..., v^1_k, ..., v^m_1, ..., v^m_k, s_1, ..., s_k for k = f_degree *)
    f_gray: BI.big_int;
}


let iter_to_ints iter =
    let (k: int) = List.length iter.f_names in
    let extract_val (neg_zeroes, ints) (i: int) =
        let rec collect_val (shift: int) (j: int) =
            if j >= iter.f_degree
            then BI.zero_big_int
            else begin
                let (pos: int) = k + i + j * k in
                let (bit: BI.big_int) = BI.extract_big_int iter.f_gray pos 1 in
                (*printf "  i = %d, j = %d, pos = %d, bit = %s\n"
                    i j pos (BI.to_string bit);*)
                BI.add_big_int
                    (BI.shift_left_big_int bit shift)
                    (collect_val (shift + 1) (j + 1))
            end
        in
        let value = BI.int_of_big_int (collect_val 0 0) in
        let sign_pos = i in
        let sign_bit = BI.extract_big_int iter.f_gray sign_pos 1 in
        if BI.equal sign_bit BI.zero_big_int
        then (neg_zeroes, value :: ints)                    (* positive *)
        else ((value = 0) || neg_zeroes, (-value) :: ints)  (* negative *)
    in
    let neg_zeroes, ints = 
        List.fold_left extract_val (false, []) (range 0 k)
    in
    (neg_zeroes, List.rev ints)


let iter_to_unknowns_vec iter =
    let _, ints = iter_to_ints iter in
    let exprs = List.map (fun i -> IntConst i) ints in
    List.combine iter.f_names exprs


let map_of_unknowns_vec (vec: (string * Spin.token SpinIr.expr) list) =
    let add map (name, exp) = StrMap.add name exp map in
    List.fold_left add StrMap.empty vec


(** compute the initial vector of unknowns *)
let vec_iter_init sk (degree: int) =
    (* fill the last k bits with ones *)
    let rec all_ones n =
        (* 2 * x + 1 *)
        if n > 0
        then BI.succ_big_int (BI.shift_left_big_int (all_ones (n - 1)) 1)
        else BI.zero_big_int
    in
    let k = List.length sk.Sk.unknowns in
    {
        f_names = List.map (fun v -> v#get_name) sk.Sk.unknowns;
        f_degree = degree;
        f_gray = all_ones k; (* 00000(1)^k, i.e., all signs are set to 1 *)
    }


(** compute the next vector of unknowns *)
let rec vec_iter_next iter =
    let next_gray = BI.succ_big_int iter.f_gray in
    (*printf "  next = %s\n" (BI.to_string next_gray);*)
    let next_iter = {iter with f_gray = next_gray} in
    let neg_zeroes, next_ints = iter_to_ints next_iter in
    (*printf "next_ints = [%s]\n"
        (str_join ", " (List.map string_of_int next_ints));*)
    if neg_zeroes
    then vec_iter_next next_iter (* ignore values with -0 *)
    else next_iter


let vec_iter_end iter =
    let k = List.length iter.f_names in
    let beyond =
        BI.shift_left_big_int BI.unit_big_int (k + k * iter.f_degree)
    in
    (*printf "  beyond = %s\n" (BI.to_string beyond);*)
    BI.ge_big_int iter.f_gray beyond


let unknowns_vec_s vec =
    let pair_s (n, e) =
        sprintf "%s = %s" n (SpinIrImp.expr_s e)
    in
    str_join ", " (List.map pair_s vec)


(** replace unknowns with the values given in the unknowns vector *)
let replace_unknowns sk unknowns_vec =
    let vec_map = map_of_unknowns_vec unknowns_vec in
    let sub exp =
        let map_fun v =
            try StrMap.find v#get_name vec_map
            with Not_found -> Var v
        in
        Simplif.compute_consts (map_vars map_fun exp)
    in
    let map_rule r =
        { r with Sk.guard = sub r.Sk.guard;
                 Sk.act = List.map sub r.Sk.act }
    in
    { sk with Sk.unknowns = [];
              Sk.assumes = List.map sub sk.Sk.assumes;
              Sk.rules = List.map map_rule sk.Sk.rules;
              Sk.inits = List.map sub sk.Sk.inits }


(** check, whether a counterexample is applicable to the skeleton *)    
let is_cex_applicable sk cex =
    let get_int = function
        | IntConst i -> i
        | _ as e ->
            raise (Failure ("Expected IntConst _, found %s" ^ (SpinIrImp.expr_s e)))
    in
    let bind state var =
        try IntConst (StrMap.find var#get_name state)
        with Not_found -> Var var
    in
    let apply_action state = function
        | BinEx (EQ, UnEx (NEXT, Var lhs), rhs) ->
            let rhs_val =
                Simplif.compute_consts (SpinIr.map_vars (bind state) rhs)
            in
            StrMap.add lhs#get_name (get_int rhs_val) state
            
        | _ as e ->
            let m = "Unexpected action: " ^ (SpinIrImp.expr_s e) in
            raise (Failure m)
    in
    let rec is_app state = function
        | [] ->
            true    (* no moves left *)

        | m :: tl ->    (* check the guard of the rule associated with m *)
            let r = List.nth sk.Sk.rules m.C.f_rule_no in
            let guard_val = Simplif.compute_consts
                (SpinIr.map_vars (bind state) r.Sk.guard)
            in
            match guard_val with
            | IntConst 0 ->
                (* the guard evaluates to false *)
                false

            | IntConst 1 ->
                (* the guard evaluates to true, go on *)
                let next_state =
                    List.fold_left apply_action state r.Sk.act
                in
                is_app next_state tl

            | _ as e ->
                let m = sprintf "Unexpected outcome of the guard %s: %s"
                    (SpinIrImp.expr_s r.Sk.guard) (SpinIrImp.expr_s guard_val)
                in
                raise (Failure m)
    in
    is_app cex.C.f_init_state cex.C.f_moves

