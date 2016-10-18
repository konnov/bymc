open Batteries
open Printf

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


module Ta = struct
    type loc_def_t = string * int list

    type rule_t =
        { src_loc: int; dst_loc: int; guard: bool_expr_t; action: bool_expr_t }


    type ta_t = {
        name: string;
        decls: decl_t list;
        assumptions: rel_expr_t list;
        locs: loc_def_t list;
        inits: rel_expr_t list;
        rules: rule_t list;
    }
end

let empty =
    { Ta.name = ""; Ta.decls = []; Ta.assumptions = [];
      Ta.locs = []; Ta.inits = []; Ta.rules = []; }


let mk_rule src_loc dst_loc guard action =
    { Ta.src_loc; Ta.dst_loc; Ta.guard; Ta.action }


let mk_ta n ds ass ls is rs =
    { Ta.name = n; Ta.decls = ds; Ta.assumptions = ass;
      Ta.locs = ls; Ta.inits = is; Ta.rules = rs; }


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
    fprintf out "  ";
    print expr;
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
    List.iter (print_rel_expr out) ta.Ta.assumptions;
    List.iter (print_loc out) ta.Ta.locs;
    List.iter (print_rel_expr out) ta.Ta.inits;
    fprintf out "}\n";

