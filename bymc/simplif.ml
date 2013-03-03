(*
 * Simplify MIR statements:
 *   * convert array access to a variable access.
 *)

open Printf

open Accums
open Spin
open SpinIr
open SpinIrEval
open SpinIrImp

module VarMap = Map.Make (struct
 type t = var
 let compare a b = a#id - b#id
end)

exception Simplif_error of string

(* find bindings for all variables used in an expression *)
let mk_expr_bindings type_tab exp =
    let not_array v = not (type_tab#get_type v)#is_array in
    let used_vars = List.filter not_array (expr_used_vars exp) in
    let get_var_range v =
        let tp = type_tab#get_type v in
        if tp#is_array
        then raise (Simplif_error
            (sprintf "Expression %s has an array access %s"
                (expr_s exp) v#get_name))
        else if not tp#has_range
        then raise
            (Simplif_error (sprintf "%s does not have range assigned" v#get_name))
        else let l, r = tp#range in
            range l r
    in
    let mk_var_map tuple =
        let bind map var value = VarMap.add var value map in
        List.fold_left2 bind VarMap.empty used_vars tuple
    in
    let var_ranges = List.map get_var_range used_vars in
    if used_vars = []
    then []
    else
        let all_tuples = mk_product_of_lists var_ranges in
        List.map mk_var_map all_tuples


(* replace array accesses like  a[x+y] == i by a conjunction:
    (x == 0 && y == 0 && a[0] == i) || ... || (x == m && y == n && a[m+n] == i)
 *)
let expand_arrays type_tab expr =
    let is_arr_access = function
    | BinEx (ARR_ACCESS, _, _) -> true
    | _ -> false
    in
    (* TODO: compute constant expressions *)
    let prop_const exp binding =
        let rec prop_rec = function
        | Var v ->
            if VarMap.mem v binding
            then Const (VarMap.find v binding)
            else Var v

        | UnEx (tok, e) -> UnEx (tok, (prop_rec e))
        | BinEx (tok, l, r) -> BinEx (tok, (prop_rec l), (prop_rec r))
        | _ as e -> e
        in
        prop_rec exp
    in
    let binding_to_eqs binding =
        let eq (var, value) = BinEx (EQ, Var var, Const value) in
        List.map eq (VarMap.bindings binding)
    in
    let rec expand = function
    | BinEx (EQ, _, _) 
    | BinEx (NE, _, _)
    | BinEx (GT, _, _) 
    | BinEx (GE, _, _)
    | BinEx (LT, _, _) 
    | BinEx (LE, _, _) as e ->
        let prop e binding =
            list_to_binex AND ((prop_const e binding) :: binding_to_eqs binding)
        in
        if expr_exists is_arr_access e
        then
            let bindings = mk_expr_bindings type_tab e in
            let instances = List.map (prop e) bindings in
            list_to_binex OR instances
        else e
            
    | UnEx (t, e) -> UnEx (t, (expand e))
    | BinEx (t, l, r) -> BinEx (t, (expand l), (expand r))
    | _ as e -> e
    in
    expand expr


let simplify type_tab mir_stmt =
    let rec simp = function
    | MExpr (id, e) ->
        MExpr (id, expand_arrays type_tab e)
    | MIf (id, opts) ->
        MIf (id, (List.map simp_opt opts))
    | MAtomic (id, body) ->
        MAtomic (id, List.map simp body)
    | MD_step (id, body) ->
        MD_step (id, List.map simp body)
    | _ as s -> s

    and simp_opt = function
    | MOptGuarded body ->
        MOptGuarded (List.map simp body)
    | MOptElse body ->
        MOptElse (List.map simp body)
    in
    simp mir_stmt

let simplify_prog caches prog =
    let type_tab = Program.get_type_tab prog in
    let simp_proc p =
        proc_replace_body p (List.map (simplify type_tab) p#get_stmts)
    in
    Program.set_procs (List.map simp_proc (Program.get_procs prog)) prog
        
