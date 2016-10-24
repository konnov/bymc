open Batteries
open Printf

open Accums

type decl_t =
    | Local of string
    | Shared of string
    | Param of string


type arith_expr_t =
    | Int of int
    | Var of string
    | NextVar of string
    | Add of arith_expr_t * arith_expr_t
    | Sub of arith_expr_t * arith_expr_t
    | Mul of arith_expr_t * arith_expr_t


type rel_expr_t =
    | Eq of arith_expr_t * arith_expr_t
    | Neq of arith_expr_t * arith_expr_t
    | Lt of arith_expr_t * arith_expr_t
    | Leq of arith_expr_t * arith_expr_t
    | Gt of arith_expr_t * arith_expr_t
    | Geq of arith_expr_t * arith_expr_t


type bool_expr_t =
    | Cmp of rel_expr_t
    | Not of bool_expr_t
    | And of bool_expr_t * bool_expr_t
    | Or of bool_expr_t * bool_expr_t


type action_t = string  * arith_expr_t


type ltl_expr_t =
    | LtlCmp of rel_expr_t
    | LtlNot of ltl_expr_t
    | LtlAnd of ltl_expr_t * ltl_expr_t
    | LtlOr of ltl_expr_t * ltl_expr_t
    | LtlImplies of ltl_expr_t * ltl_expr_t
    | LtlF of ltl_expr_t
    | LtlG of ltl_expr_t


module Ta = struct
    type loc_def_t = string * int list

    type rule_t =
        { src_loc: int; dst_loc: int; guard: bool_expr_t; actions: action_t list }


    type ta_t = {
        name: string;
        decls: decl_t list;
        assumptions: rel_expr_t list;
        locs: loc_def_t list;
        inits: rel_expr_t list;
        rules: rule_t list;
        specs: ltl_expr_t StrMap.t;
    }
end

let empty =
    { Ta.name = ""; Ta.decls = []; Ta.assumptions = [];
      Ta.locs = []; Ta.inits = []; Ta.rules = [];
      Ta.specs = StrMap.empty;
    }


let mk_rule src_loc dst_loc guard actions =
    { Ta.src_loc; Ta.dst_loc; Ta.guard; Ta.actions }


let mk_ta n ds ass ls is rs specs =
    { Ta.name = n; Ta.decls = ds; Ta.assumptions = ass;
      Ta.locs = ls; Ta.inits = is; Ta.rules = rs; Ta.specs = specs }


let print_arith_expr out expr =
    let rec pr = function
        | Int i -> fprintf out "%d" i
        | Var n -> fprintf out "%s" n
        | NextVar n -> fprintf out "%s'" n
        | Add (l, r) -> pr l; fprintf out " + "; pr r
        | Sub (l, r) -> pr l; fprintf out " - "; pr r
        | Mul (l, r) -> pr l; fprintf out " * "; pr r
    in
    pr expr


let print_rel_expr out expr =
    let pr op l r =
        print_arith_expr out l;
        fprintf out op;
        print_arith_expr out r
    in
    let print = function
        | Gt (l, r) -> pr " > " l r
        | Geq (l, r) -> pr " >= " l r
        | Lt (l, r) -> pr " < " l r
        | Leq (l, r) -> pr " <= " l r
        | Neq (l, r) -> pr " != " l r
        | Eq (l, r) -> pr " == " l r
    in
    print expr


let print_rel_expr_with_semi out expr =
    fprintf out "  ";
    print_rel_expr out expr;
    fprintf out ";\n"


let print_ltl_expr out name expr =
    let rec pr = function
        | LtlCmp e ->
            fprintf out "(";
            print_rel_expr out e;
            fprintf out ")"

        | LtlNot e ->
            fprintf out "!("; pr e; fprintf out ")"

        | LtlAnd (l, r) ->
            fprintf out "("; pr l; fprintf out ")";
            fprintf out " && ";
            fprintf out "("; pr r; fprintf out ")"

        | LtlOr (l, r) ->
            fprintf out "("; pr l; fprintf out ")";
            fprintf out " || ";
            fprintf out "("; pr r; fprintf out ")"

        | LtlImplies (l, r) ->
            fprintf out "("; pr l; fprintf out ")";
            fprintf out " -> ";
            fprintf out "("; pr r; fprintf out ")"

        | LtlF e ->
            fprintf out "<>("; pr e; fprintf out ")"

        | LtlG e ->
            fprintf out "[]("; pr e; fprintf out ")"
    in
    fprintf out "  %s: " name;
    pr expr;
    fprintf out ";\n"


let print_loc out (name, vals) =
    let p i = fprintf out "%d; " i in
    fprintf out "  %s: [" name;
    List.iter p vals;
    fprintf out "];\n"


let print_ta out ta =
    fprintf out "\nskel %s {\n" ta.Ta.name;   
    let print_decl = function
        | Local name -> fprintf out "  local %s;\n" name
        | Shared name -> fprintf out "  shared %s;\n" name
        | Param name -> fprintf out "  parameters %s;\n" name
    in
    List.iter print_decl ta.Ta.decls;
    List.iter (print_rel_expr_with_semi out) ta.Ta.assumptions;
    List.iter (print_loc out) ta.Ta.locs;
    List.iter (print_rel_expr_with_semi out) ta.Ta.inits;
    StrMap.iter (print_ltl_expr out) ta.Ta.specs;
    fprintf out "}\n";

