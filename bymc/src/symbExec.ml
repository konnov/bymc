(*
 * Executing a path symbolically and collecting the constraints
 * along it.
 *
 * Igor Konnov, 2013-2014
 *)

open Accums
open Cfg
open Printf
open Simplif
open Spin
open SpinIr
open SpinIrImp

exception SymbExec_error of string

let linearize_blocks (path: token basic_block list) =
    let seq = List.concat (List.map (fun b -> b#get_seq) path) in
    let is_lin_stmt = function
    | Expr (_, Nop _) -> false
    | Expr (_, _) -> true
    | Decl (_, _, _) -> true
    | Assert (_, _) -> true
    | Assume (_, _) -> true
    | Havoc (_, _) -> true
    | _ -> false (* ignore everything else *)
    in
    List.filter is_lin_stmt seq


let sub_vars vals exp =
    let sub v =
        if Hashtbl.mem vals v#get_name
        then Hashtbl.find vals v#get_name
        else Var v
    in
    compute_consts (map_vars sub exp)


let check_sat solver type_tab exp =
    if is_c_true exp
    then true
    else if is_c_false exp
    then false
    else begin
        let vars = expr_used_vars exp in
        let add_var v =
            let t = type_tab#get_type v in
            solver#append_var_def v t
        in
        solver#push_ctx;
        List.iter add_var vars;
        solver#append_expr exp;
        let res = solver#check in
        solver#pop_ctx;
        res
    end


let inc_version sym_tab type_tab var ver =
    let new_name = sprintf "%s$%d" var#get_name (ver + 1) in
    let nv =
        try (sym_tab#lookup new_name)#as_var
        with Symbol_not_found _ ->
            let c = var#copy new_name in
            sym_tab#add_symb new_name (c :> symb);
            type_tab#set_type c (type_tab#get_type var);
            c
    in
    nv


(* please, no arrays here *)
let exec_stmt sym_tab type_tab versions vals path_cons = function
    | Expr (_, BinEx (ASGN, Var v, rhs)) ->
        let new_rhs = sub_vars vals rhs in
        Hashtbl.replace vals v#get_name new_rhs;
        path_cons

    | Havoc (_, v) ->
        (* this is the only place,
           where we have to introduce a new variable *)
        let ver = Hashtbl.find versions v#get_name in
        let nv = inc_version sym_tab type_tab v ver in 
        Hashtbl.replace versions v#get_name (ver + 1);
        Hashtbl.replace vals v#get_name (Var nv);
        path_cons

    | Assume (_, e)
    | Expr (_, e) ->
        let ne =
            try sub_vars vals e
            with SymbExec_error s ->
                raise (SymbExec_error (s ^ " in: " ^ (expr_s e)))
        in
        if is_c_true path_cons
        then ne
        else BinEx (AND, path_cons, ne)

    | _ -> path_cons



let exec_path solver (type_tab: data_type_tab) (sym_tab: symb_tab)
        (vars: var list)
        (path_fun: token expr -> (string, token expr) Hashtbl.t -> unit)
        (path: token basic_block list) (is_final: bool) =
    (* WARNING: we are reusing variables in sym_tab! *)
    let stmts = linearize_blocks path in
    let versions = Hashtbl.create 10 in
    let vals = Hashtbl.create 10 in
    let add_input v =
        Hashtbl.add versions v#get_name 0;
        Hashtbl.add vals v#get_name (Var v)
    in
    List.iter add_input vars;

    let path_cons =
        try List.fold_left
            (exec_stmt sym_tab type_tab versions vals) (IntConst 1) stmts
        with SymbExec_error s ->
            printf "The troublesome path is:\n";
            List.iter (fun s -> printf "  %s\n" (stmt_s s)) stmts;
            raise (SymbExec_error s)
    in
    let path_cons = compute_consts path_cons in
    let is_sat = check_sat solver type_tab path_cons in

    if is_final && is_sat then path_fun path_cons vals;
    is_sat

