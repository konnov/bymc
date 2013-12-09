(*
  Operations on bit vectors encoded as SAT.

  Igor Konnov, 2011-2013
 *)

open List
open Printf

open Sat
open Accums

exception VarNotFound of string

(* a convenient language over bit vectors *)
type bv_form =
    | B1 | B0 | V of string | NV of string
    | EQ of string * string | NE of string * string
    | LT of string * string | LE of string * string
    | GT of string * string | GE of string * string
    | VeqI of string * int
    | VneI of string * int
    | AND of bv_form list | OR of bv_form list
    | ANNOTATION of string * bv_form (* a comment wrapping a subformula *)

type bitvar_type = { len: int; hidden: bool }

let rec bv_form_s = function
      | B1 -> "1"
      | B0 -> "0"
      | V x -> x
      | NV x -> "!" ^ x
      | EQ(x, y) -> x ^ " == " ^ y
      | NE(x, y) -> x ^ " != " ^ y
      | LT(x, y) -> x ^ " < " ^ y
      | LE(x, y) -> x ^ " <= " ^ y
      | GT(x, y) -> x ^ " > " ^ y
      | GE(x, y) -> x ^ " >= " ^ y
      | VeqI(x, ival) -> sprintf "%s = %d" x ival
      | VneI(x, ival) -> sprintf "%s != %d" x ival

      | AND lst ->
            let concat s f =
                let pref = if s <> "" then " & " else "" in
                (pref ^ "(" ^ (bv_form_s f) ^ ")")
            in
            List.fold_left concat "" lst

      | OR lst ->
            let concat s f =
                let pref = if s <> "" then " | " else "" in
                (pref ^ "(" ^ (bv_form_s f) ^ ")")
            in
            List.fold_left concat "" lst

      | ANNOTATION(_, subform) -> bv_form_s subform


let rec neg_bf_form = function
      | B1 -> B1
      | B0 -> B1
      | V x -> NV x
      | NV x -> V x
      | EQ(x, y) -> NE(x, y)
      | NE(x, y) -> EQ(x, y)
      | LT(x, y) -> GE(x, y)
      | LE(x, y) -> GT(x, y)
      | GT(x, y) -> LE(x, y)
      | GE(x, y) -> LT(x, y)
      | VeqI(x, ival) -> VneI(x, ival)
      | VneI(x, ival) -> VeqI(x, ival)
      | AND lst -> OR (List.rev_map neg_bf_form lst)
      | OR lst -> AND (List.rev_map neg_bf_form lst)
      | ANNOTATION(text, subform) ->
          ANNOTATION(text, neg_bf_form subform)


let rec format_bv_form ff = function
      | B1 -> Format.fprintf ff "1"
      | B0 -> Format.fprintf ff "0"
      | V x -> Format.fprintf ff "%s" x
      | NV x -> Format.fprintf ff "~%s" x
      | EQ(x, y) -> Format.fprintf ff "%s == %s" x y
      | NE(x, y) -> Format.fprintf ff "%s != %s" x y
      | LT(x, y) -> Format.fprintf ff "%s < %s" x y
      | LE(x, y) -> Format.fprintf ff "%s <= %s" x y
      | GT(x, y) -> Format.fprintf ff "%s > %s" x y
      | GE(x, y) -> Format.fprintf ff "%s >= %s" x y
      | VeqI(x, ival) -> Format.fprintf ff "%s = %d" x ival
      | VneI(x, ival) -> Format.fprintf ff "%s != %d" x ival
      | AND lst ->
        Format.fprintf ff "@[<1>";
        let print first form =
            if first
            then Format.fprintf ff "%s" "("
            else Format.fprintf ff "@ @,&@ %s" "(";
            format_bv_form ff form;
            Format.fprintf ff ")";
            false
        in
        List.fold_left print true lst;
        Format.fprintf ff "@]"
      | OR lst ->
        Format.fprintf ff "@[<1>";
        let print first form =
            if first
            then Format.fprintf ff "%s" "("
            else Format.fprintf ff "@ @,|@ %s" "(";
            format_bv_form ff form;
            Format.fprintf ff ")";
            false
        in
        List.fold_left print true lst;
        Format.fprintf ff "@]"
      | ANNOTATION(text, subform) ->
        Format.fprintf ff "  /* %s */@\n" text;
        format_bv_form ff subform


let ivar_s x idx = (sprintf "%s_%d" x idx)


(* generate the list of boolean variable names corresponding
   to one bit-vector variable *)
let mk_bool_var_names name bit_type =
    List.rev_map (ivar_s name) (rev_range 1 (bit_type.len + 1))


let rec mk_eq x y x_sz y_sz =
    if x_sz != y_sz
    then raise
        (Invalid_argument
            (sprintf "Var %s and %s have different bit lengths (%d and %d)"
                x y x_sz y_sz))
    else
    if x_sz = 0
    then []
    else (List.rev_append
                [Or[Not (Var(ivar_s x x_sz)); Var(ivar_s y y_sz)];
                 Or[Var(ivar_s x x_sz); Not (Var(ivar_s y y_sz))]]
                (mk_eq x y (x_sz - 1) (y_sz - 1)))


(*
  Optimized to generate a better CNF. Later found that the same trick was
  presented in: Biere, Brummayer. Consistency Checking of All Different
  Constraints over Bit-Vectors within a SAT Solver, 2008.
 *)
let mk_ne x y x_sz y_sz aux_pool =
    let rec mk_ne_clauses n =
        if n = 0
        then ([], [])
        else
            let z = aux_pool#next_aux in
            let vx, vy = Var(ivar_s x n), Var(ivar_s y n) in
            let cond1 = Or[vx; vy; Not(z)] in
            let cond2 = Or[Not(vx); Not(vy); Not(z)] in
            let (zs, clauses) = (mk_ne_clauses (n - 1)) in
            (z::zs, cond1 :: cond2 :: clauses)
    in
    if x_sz != y_sz
    then raise
        (Invalid_argument (sprintf "Var %s and %s differ in bit length" x y))
    else
    if x_sz = 0
    then []
    else let (zs, clauses) = mk_ne_clauses x_sz
    in Or(zs) :: clauses


let rec mk_lt x y x_sz y_sz carry_z aux_pool =
    if x_sz != y_sz
    then raise
        (Invalid_argument (sprintf "Var %s and %s differ in bit length" x y))
    else
    if x_sz = 1 && carry_z = True
    then [Not(Var(ivar_s x 1)); Var(ivar_s y 1)]
    else if x_sz = 1
    then [Or[Not(carry_z); Not(Var(ivar_s x 1))];
          Or[Not(carry_z); Var(ivar_s y 1)]]
    else let aux_var = aux_pool#next_aux in
        (List.rev_append
                [Or[Var(ivar_s y y_sz); Not(Var(ivar_s x x_sz))];
                 Or[Not(Var(ivar_s x x_sz)); aux_var];
                 Or[Not(Var(ivar_s y y_sz)); aux_var]]
            (mk_lt x y (x_sz - 1) (y_sz - 1) aux_var aux_pool))


let rec mk_le x y x_sz y_sz carry_z aux_pool =
    if x_sz != y_sz
    then raise
        (Invalid_argument (sprintf "Var %s and %s differ in bit length" x y))
    else
    if x_sz = 1 && carry_z = True
    then [Or[Not (Var(ivar_s x 1)); Var(ivar_s y 1)]]
    else if x_sz = 1
    then [Or[Not(carry_z);
            Or[Not(Var(ivar_s x 1)); Var(ivar_s y 1)]]]
    else let aux_var = aux_pool#next_aux in
        (List.rev_append
                [Or[Var(ivar_s y y_sz); Not(Var(ivar_s x x_sz))];
                 Or[Not(Var(ivar_s x x_sz)); aux_var];
                 Or[Not(Var(ivar_s y y_sz)); aux_var]]
            (mk_le x y (x_sz - 1) (y_sz - 1) aux_var aux_pool))


let rec mk_eq_with_const x len ival positive =
    let rec to_bin x len i v parts =
        if i > len then parts
        else
          let var_expr = if ((v mod 2) = positive)
            then (Var (ivar_s x i))
            else Not(Var (ivar_s x i))
          in
          (to_bin x len (i + 1) (v / 2) (var_expr :: parts))
        in
    let collected = (to_bin x len 1 ival []) in
    if positive = 1 then And(collected) else Or(collected)


(*
  Transform a bit-vector formula to a boolean formula
  (close to CNF if possible)
*)
let rec to_sat bv_types aux_pool bv_frm =
    let get_var_len x =
        try (StringMap.find x bv_types).len
        with Not_found -> raise (VarNotFound x)
    in
    match bv_frm with
      | B1 -> True
      | B0 -> False
      | V x ->
            if (get_var_len x) = 1
            then Var (x ^ "_1")
            else raise (Invalid_argument ("Var " ^ x ^ " is longer than 1 bit"))
      | NV x -> Not (to_sat bv_types aux_pool (V x))
      | EQ(x, y) ->
              And(mk_eq x y (get_var_len x) (get_var_len y))
      | NE(x, y) ->
              And(mk_ne x y (get_var_len x) (get_var_len y) aux_pool)
      | LT(x, y) ->
              And(mk_lt x y
                (get_var_len x) (get_var_len y)
                True aux_pool)
      | LE(x, y) ->
              And(mk_le x y
                (get_var_len x) (get_var_len y)
                True aux_pool)
      | GT(x, y) ->
              And(mk_lt y x
                (get_var_len y) (get_var_len x)
                True aux_pool)
      | GE(x, y) ->
              And(mk_le y x
                (get_var_len y) (get_var_len x)
                True aux_pool)
      | VeqI(x, ival) ->
              let len = (get_var_len x) in
              mk_eq_with_const x len ival 1
      | VneI(x, ival) ->
              let len = (get_var_len x) in
              mk_eq_with_const x len ival 0
      | AND lst ->
              And(List.rev (List.rev_map (to_sat bv_types aux_pool) lst));
      | OR lst ->
              Or(List.rev (List.rev_map (to_sat bv_types aux_pool) lst));
      | ANNOTATION(_, subform) ->
              to_sat bv_types aux_pool subform


let bitsat_to_cnf bit_vars aux_pool bitsat_form =
    let first_id = aux_pool#get_free_id in
    let cnf_form = (cnfify aux_pool (to_sat bit_vars aux_pool bitsat_form)) in
    let next_id = aux_pool#get_free_id in
    { sat_form = cnf_form; first_id = first_id;
      num_aux_vars = (next_id - first_id) }


let map_bit_vars_to_dimacs bit_vars first_id =
    let map_one name bit_type (i_map, i_id) =
        if String.contains name '{'
        then (i_map, i_id)
        else List.fold_left
            (fun (map, id) i ->
                let new_name = (Printf.sprintf "%s_%d" name i) in
                let new_map = (StringMap.add new_name id map) in
                (*Printf.printf "  map: %s -> %d\n" new_name id;*)
                (new_map, (id + 1))
            )
            (i_map, i_id)
            (range 1 (bit_type.len + 1))
    in
    StringMap.fold
        map_one
        bit_vars
        (StringMap.empty, first_id)


(*
Create a vector of variable identifiers describing a global state for
a given layer.
 *)
let mk_state_vector_ids bit_vars bool_vars layer_no =
    let map_one name bit_type vec =
        if ((str_contains name ("[" ^ (string_of_int layer_no) ^ "]"))
            && not bit_type.hidden)
        then (List.rev_append (mk_bool_var_names name bit_type) vec)
        else vec
    in
    let names = StringMap.fold map_one bit_vars []
    in
    let get_var_index n =
        try
            StringMap.find n bool_vars
        with Not_found ->
            raise (Invalid_argument
                (Printf.sprintf "Bool variable %s not found" n))
    in
    List.rev_map get_var_index names


let bits_to_fit n =
    let rec f b m =
        if n <= m
        then b
        else f (b + 1) (2 * m)
    in
    f 1 2


let fold_bit_var lit_lst pref =
    let rec pow2 n =
        if n <= 0 then 1 else 2 * (pow2 (n - 1))
    in
    List.fold_left
        (fun sum v ->
            if (Str.string_match (Str.regexp ("^" ^ pref ^ "_\\([0-9]+\\)")) v 0)
            then (pow2 ((int_of_string (Str.matched_group 1 v)) - 1)) + sum
            else sum)
        0
        lit_lst

