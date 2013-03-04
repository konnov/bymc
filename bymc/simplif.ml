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


(* propagate constants *)
let prop_const exp binding =
    let compute tok le re =
        match tok, le, re with
        | PLUS, Const l, Const r -> Const (l + r)
        | MINUS, Const l, Const r -> Const (l - r)
        | MULT, Const l, Const r -> Const (l * r)
        | DIV, Const l, Const r -> Const (l / r)
        | _ -> BinEx (tok ,le, re)
    in
    let rec prop_rec = function
    | Var v ->
        if VarMap.mem v binding
        then Const (VarMap.find v binding)
        else Var v

    | BinEx (PLUS, l, r) ->
        compute PLUS (prop_rec l) (prop_rec r)

    | BinEx (MINUS, l, r) ->
        compute MINUS (prop_rec l) (prop_rec r)

    | BinEx (MULT, l, r) ->
        compute MULT (prop_rec l) (prop_rec r)

    | BinEx (DIV, l, r) ->
        compute DIV (prop_rec l) (prop_rec r)

    | UnEx (tok, e) ->
        UnEx (tok, (prop_rec e))

    | BinEx (tok, l, r) ->
        BinEx (tok, (prop_rec l), (prop_rec r))
    | _ as e -> e
    in
    prop_rec exp


(* replace array accesses like  a[x+y] == i by a conjunction:
    (x == 0 && y == 0 && a[0] == i) || ... || (x == m && y == n && a[m+n] == i)
 *)
let expand_arrays type_tab stmt =
    let is_arr_access = function
    | BinEx (ARR_ACCESS, _, _) -> true
    | _ -> false
    in
    let binding_to_eqs binding =
        let eq (var, value) = BinEx (EQ, Var var, Const value) in
        List.map eq (VarMap.bindings binding)
    in
    let rec expand = function
    | MExpr (id, BinEx (EQ, _, _))
    | MExpr (id, BinEx (NE, _, _))
    | MExpr (id, BinEx (GT, _, _))
    | MExpr (id, BinEx (GE, _, _))
    | MExpr (id, BinEx (LT, _, _))
    | MExpr (id, BinEx (LE, _, _)) as s ->
        let prop e binding =
            list_to_binex AND ((prop_const e binding) :: binding_to_eqs binding)
        in
        let e = expr_of_m_stmt s in
        if expr_exists is_arr_access e
        then
            let bindings = mk_expr_bindings type_tab e in
            if bindings <> []
            then let instances = List.map (prop e) bindings in
                MExpr (id, list_to_binex OR instances)
            else s
        else s

    | MExpr (id, BinEx (ASGN, _, _)) as s ->
        let mk_opt e binding =
            let guard =
                MExpr(-1, (list_to_binex AND (binding_to_eqs binding))) in
            MOptGuarded [guard; MExpr(-1, (prop_const e binding))]
        in
        let e = expr_of_m_stmt s in
        if expr_exists is_arr_access e
        then
            let bindings = mk_expr_bindings type_tab e in
            if bindings <> []
            then let options = List.map (mk_opt e) bindings in
                MIf (id, options) (* many options *)
            else s (* constant indices *)
        else s
            
    | MExpr (id, UnEx (t, e)) ->
        let sube = expr_of_m_stmt (expand (MExpr (-1, e))) in
        MExpr (id, UnEx (t, sube))

    | MExpr (id, BinEx (t, l, r)) ->
        let le = expr_of_m_stmt (expand (MExpr (-1, l))) in
        let re = expr_of_m_stmt (expand (MExpr (-1, r))) in
        MExpr (id, BinEx (t, le, re))

    | _ as s -> s
    in
    expand stmt


let flatten_arrays type_tab new_type_tab stmts =
    let flatten_rev collected = function
    | MDecl (id, v, _) as s ->
        let tp = type_tab#get_type v in
        let mk_var i =
            let nv = v#fresh_copy (sprintf "%s_%d" v#get_name i) in
            let nt = tp#copy in
            nt#set_nelems 1;
            new_type_tab#set_type nv nt;
            MDecl (-1, nv, Nop "")
        in
        if tp#is_array
        then (List.map mk_var (range 0 tp#nelems)) @ collected
        else s :: collected

    | _ as s -> s :: collected
    in
    List.rev (List.fold_left flatten_rev [] stmts)


let simplify type_tab new_type_tab mir_stmt =
    let rec simp = function
    | MExpr (_, _) as s ->
        expand_arrays type_tab s
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
    let new_type_tab = type_tab#copy in
    let simp_proc p =
        let new_stmts = List.map (simplify type_tab new_type_tab) p#get_stmts in
        let new_stmts = flatten_arrays type_tab new_type_tab new_stmts in
        proc_replace_body p new_stmts
    in
    let new_procs = (List.map simp_proc (Program.get_procs prog)) in
    Program.set_type_tab new_type_tab
        (Program.set_procs new_procs prog)
        
