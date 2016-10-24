(**
 * A threshold automaton (see CONCUR'14, CAV'15 papers).
 * This representation is a mirror of SymbSkel. We just need it
 * to implement TaParser without using Spinlex.
 *
 * @author Igor Konnov, 2015
 *)


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


module Ta: sig
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
        specs: ltl_expr_t Accums.StrMap.t;
    }
end

val empty: Ta.ta_t

val mk_rule:
    int -> int -> bool_expr_t -> action_t list -> Ta.rule_t


val mk_ta:
    string -> decl_t list -> rel_expr_t list
           -> Ta.loc_def_t list -> rel_expr_t list -> Ta.rule_t list
           -> ltl_expr_t Accums.StrMap.t
           -> Ta.ta_t

val print_ta:
    unit BatIO.output -> Ta.ta_t -> unit

