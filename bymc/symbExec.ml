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
    (String.length n) > 0 && (String.get n 0) = '$'


let mk_input (v: var): var =
    new var ("$" ^ v#get_name) (fresh_id ())


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


let exec_path (path: token basic_block list) =
    let vals = Hashtbl.create 10 in
    let add_input v =
        Hashtbl.add vals v#id (Var (mk_input v))
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
    printf "  Path constraint: %s\n" (expr_s path_cons);
    let print_var v =
        let exp = Hashtbl.find vals v#id in
        printf "  %s = %s\n" v#get_name (expr_s exp)
    in
    List.iter print_var vars

