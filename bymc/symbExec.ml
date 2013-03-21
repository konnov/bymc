(* Executing a path symbolically and collecting the constraints along it
 *
 * Igor Konnov, 2013
 *)

open Cfg
open Printf
open Spin
open SpinIr
open SpinIrImp

type var_cons_tbl = (string, int) Hashtbl.t

let is_input (v: var): bool =
    let n = v#get_name in
    (String.length n) > 0 && (String.get n 0) = 'O'


let mk_input (type_tab: data_type_tab) (v: var): var =
    let nv = new var ("O" ^ v#get_name) (fresh_id ()) in
    let _ = type_tab#set_type nv (type_tab#get_type v) in
    nv


let linearize_blocks (path: token basic_block list) =
    let seq = List.concat (List.map (fun b -> b#get_seq) path) in
    let is_lin_stmt = function
    | Expr (_, _) -> true
    | Decl (_, _, _) -> true
    | Assert (_, _) -> true
    | Assume (_, _) -> true
    | Havoc (_, _) -> true
    | _ -> false (* ignore anything else *)
    in
    List.filter is_lin_stmt seq


let sub_vars vals exp =
    let sub v =
        if not (is_input v)
        then Hashtbl.find vals v#id
        else Var v
    in
    map_vars sub exp


type simple_eval_res = TFalse | TTrue | TMaybe | Int of int

exception Eval_error of string

let uint = function
    | Int i -> i
    | _ -> raise (Eval_error ("expected int"))


let tbool_and l r =
    match (l, r) with
    | TMaybe, _ -> TMaybe
    | _, TMaybe -> TMaybe
    | TFalse, _ -> TFalse
    | _, TFalse -> TFalse
    | TTrue, TTrue -> TTrue
    | _ -> raise (Eval_error ("expected TFalse, TTrue, or TMaybe"))

let tbool_or l r =
    match (l, r) with
    | TTrue, _ -> TTrue
    | _, TTrue -> TTrue
    | TFalse, TFalse -> TFalse
    | TMaybe, _ -> TMaybe
    | _, TMaybe -> TMaybe
    | _ -> raise (Eval_error ("expected TFalse, TTrue, or TMaybe"))

let tbool_not = function
    | TTrue -> TFalse
    | TFalse -> TTrue
    | TMaybe -> TMaybe
    | _ -> raise (Eval_error ("expected TFalse, TTrue, or TMaybe"))

let is_uncertain l r =
    l = TMaybe || r = TMaybe

let mk_tbool b =
    if b then TTrue else TFalse

let is_trivially_unsat exp =
    let rec eval_expr = function
    | Const value ->
            Int value
    | Var v ->
            TMaybe
    | Nop _ ->
            TTrue
    | BinEx (EQ, le, re) ->
            let lv = eval_expr le in
            let rv = eval_expr re in
            if is_uncertain lv rv
            then TMaybe
            else mk_tbool ((uint lv) = (uint rv))
    | BinEx (NE, le, re) ->
            let lv = (eval_expr le) in
            let rv = (eval_expr re) in
            if is_uncertain lv rv
            then TMaybe
            else mk_tbool ((uint lv) <> (uint rv))
    | BinEx (GT, le, re) ->
            let lv = (eval_expr le) in
            let rv = (eval_expr re) in
            if is_uncertain lv rv
            then TMaybe
            else mk_tbool ((uint lv) > (uint rv))
    | BinEx (GE, le, re) ->
            let lv = (eval_expr le) in
            let rv = (eval_expr re) in
            if is_uncertain lv rv
            then TMaybe
            else mk_tbool ((uint lv) >= (uint rv))
    | BinEx (LT, le, re) ->
            let lv = (eval_expr le) in
            let rv = (eval_expr re) in
            if is_uncertain lv rv
            then TMaybe
            else mk_tbool ((uint lv) < (uint rv))
    | BinEx (LE, le, re) ->
            let lv = (eval_expr le) in
            let rv = (eval_expr re) in
            if is_uncertain lv rv
            then TMaybe
            else mk_tbool ((uint lv) <= (uint rv))
    | BinEx (AND, le, re) ->
            let lv = eval_expr le in
            let rv = eval_expr re in
            tbool_and lv rv
    | BinEx (OR, le, re) ->
            let lv = eval_expr le in
            let rv = eval_expr re in
            tbool_or lv rv
    | UnEx (NEG, e) ->
            tbool_not (eval_expr e)

    | BinEx (MINUS, le, re) ->
            let lv = (eval_expr le) in
            let rv = (eval_expr re) in
            if is_uncertain lv rv
            then TMaybe
            else (Int ((uint lv) - (uint rv)))
    | BinEx (PLUS, le, re) ->
            let lv = (eval_expr le) in
            let rv = (eval_expr re) in
            if is_uncertain lv rv
            then TMaybe
            else (Int ((uint lv) + (uint rv)))
    | BinEx (MULT, le, re) ->
            let lv = (eval_expr le) in
            let rv = (eval_expr re) in
            if is_uncertain lv rv
            then TMaybe
            else (Int ((uint lv) * (uint rv)))
    | BinEx (DIV, le, re) ->
            let lv = (eval_expr le) in
            let rv = (eval_expr re) in
            if is_uncertain lv rv
            then TMaybe
            else (Int ((uint lv) / (uint rv)))

    | _ as e ->
        raise (Eval_error
            (sprintf "Unknown expression to evaluate: %s" (expr_s e)))
    in
    TFalse = (eval_expr exp)


let is_sat solver type_tab exp =
    solver#push_ctx;
    let vars = expr_used_vars exp in
    let add_var v =
        let t = type_tab#get_type v in
        solver#append_var_def v t
    in
    if not_nop exp
    then begin
        List.iter add_var vars;
        solver#append_expr exp;
        let res = solver#check in
        solver#pop_ctx;
        res
    end else
        true


let path_cnt = ref 0 (* DEBUGGING, remove it afterwards *)


let exec_path solver (type_tab: data_type_tab) (path: token basic_block list) =
    let vals = Hashtbl.create 10 in
    let add_input v =
        Hashtbl.add vals v#id (Var (mk_input type_tab v))
    in
    let exec path_cons = function
    | Expr (_, BinEx (ASGN, Var v, rhs)) ->
        Hashtbl.replace vals v#id (sub_vars vals rhs);
        path_cons

    | Expr (_, e) ->
        let ne = sub_vars vals e in
        if is_nop path_cons
        then ne
        else BinEx (AND, path_cons, ne)

    | _ -> path_cons
    in
    let stmts = linearize_blocks path in
    let vars = stmt_list_used_vars stmts in
    List.iter add_input vars;
    let path_cons = List.fold_left exec (Nop "") stmts in
    if is_trivially_unsat path_cons || not (is_sat solver type_tab path_cons)
    then printf "  UNSAT\n"
    else begin
        printf "  Path constraint %d: %s\n" !path_cnt (expr_s path_cons);
        path_cnt := !path_cnt + 1;
        let print_var v =
            let exp = Hashtbl.find vals v#id in
            printf " %s = %s;" v#get_name (expr_s exp) in
        List.iter print_var vars;
        printf "\n\n"
    end

