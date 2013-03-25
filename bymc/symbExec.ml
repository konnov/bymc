(* Executing a path symbolically and collecting the constraints along it
 *
 * Igor Konnov, 2013
 *)

open Accums
open Cfg
open Printf
open Simplif
open Spin
open SpinIr
open SpinIrImp

exception SymbExec_error of string

type var_cons_tbl = (string, int) Hashtbl.t

let is_input (v: var): bool =
    let n = v#mangled_name in
    (String.length n) > 0 && (String.get n 0) = 'O'

let not_input (v: var): bool = not (is_input v)

let get_input (sym_tab: symb_tab) (v: var): var =
    let name = "O" ^ v#mangled_name in
    let sym = sym_tab#lookup name in
    sym#as_var

let get_output (sym_tab: symb_tab) (v: var): var =
    let n = v#mangled_name in
    if is_input v
    then (sym_tab#lookup (String.sub n 1 ((String.length n) - 1)))#as_var
    else v

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
        if (not_input v) && (Hashtbl.mem vals v#id)
        then Hashtbl.find vals v#id
        else Var v
    in
    compute_consts (map_vars sub exp)


type simple_eval_res = TFalse | TTrue | TMaybe | Int of int

exception Eval_error of string

let is_sat solver type_tab exp =
    solver#push_ctx;
    let vars = expr_used_vars exp in
    let add_var v =
        let t = type_tab#get_type v in
        solver#append_var_def v t
    in
    if not (is_c_true exp)
    then begin
        List.iter add_var vars;
        solver#append_expr exp;
        let res = solver#check in
        solver#pop_ctx;
        res
    end else
        true


let has_hidden_precond sym_tab hidden exp =
    let is_hidden = function
    | BinEx (EQ, Var v, Const 0)
    | BinEx (NE, Var v, Const 0) ->
    (* we cannot disable checking for zero as it might be a precondition for
       changing the variables
     *)
        false
    | BinEx (EQ, Var v, _)
    | BinEx (NE, Var v, _) ->
        let ov = get_output sym_tab v in
        List.exists (fun h -> ov#id = h#id) hidden 
    | _ -> false
    in
    expr_exists is_hidden exp


(* TODO: rewrite x = _ to TRUE for all hidden x's *)
let abstract_hidden sym_tab hidden exp = 
    let rec rewrite = function
    | BinEx (EQ, Var v, _)
    | BinEx (NE, Var v, _) as e ->
        let ov = get_output sym_tab v in
        if List.exists (fun h -> ov#id = h#id) hidden 
        then Const 1 (* TRUE *)
        else e

    | BinEx (t, l, r) ->
        BinEx (t, rewrite l, rewrite r)

    | UnEx (t, r) ->
        UnEx (t, rewrite r)

    | _ as e -> e
    in
    rewrite exp


let activate_hidden sym_tab hidden vals =
    let try_activate (n, v) =
        let exp = 
            try Hashtbl.find vals v#id
            with Not_found ->
                raise (SymbExec_error (sprintf "%s not found" v#mangled_name))
        in
        let needs_activation =
            match exp with
            | Var arg ->
                let ov = get_output sym_tab arg in
                ov#id <> v#id
            | _ ->
                true
        in
        let use_var = (sym_tab#lookup "bymc_use")#as_var in
        if needs_activation
        then begin
            Hashtbl.replace vals use_var#id (Const (n + 1)); (* activate *)
            Hashtbl.replace vals v#id (Var (get_input sym_tab v)); (* deactivate *)
        end
    in
    List.iter try_activate (List.combine (range 0 (List.length hidden)) hidden)


let indexed_var v idx = sprintf "%s_%dI" v#mangled_name idx

let smv_name sym_tab is_init v =
    let oname = (get_output sym_tab v)#mangled_name in
    if is_input v || is_init
    then oname
    else sprintf "next(%s)" oname


let path_cnt = ref 0 (* DEBUGGING, remove it afterwards *)
let print_path log =        
    fprintf log "-- PATH %d\n" !path_cnt;
    if (!path_cnt mod 1000) = 0
    then begin
        printf " visited %d paths...\n" !path_cnt;
        flush stdout;
    end;
    path_cnt := !path_cnt + 1


let exec_path solver log (type_tab: data_type_tab) (sym_tab: symb_tab)
        (shared: var list) (hidden: var list) (is_init: bool)
        (path: token basic_block list) (is_final: bool) =
    let next_fun = smv_name sym_tab is_init in
    let rec replace_arr = function
    | BinEx (ARR_ACCESS, Var arr, Const i) ->
        Var ((sym_tab#lookup (indexed_var arr i))#as_var)
    | BinEx (ARR_ACCESS, Var arr, idx_exp) ->
        raise (SymbExec_error
            (sprintf "Expected a constant index, found: %s" (expr_s idx_exp)))
    | BinEx (t, l, r) -> BinEx (t, replace_arr l, replace_arr r)
    | UnEx (t, e) -> UnEx (t, replace_arr e)
    | _ as e -> e
    in
    let get_var = function
    | Var v ->
        v
    | _ as e ->
        raise (SymbExec_error (sprintf "Expected var, found: %s" (expr_s e)))
    in
    let vals = Hashtbl.create 10 in
    let stmts = linearize_blocks path in
    let exec path_cons = function
    | Expr (_, BinEx (ASGN, BinEx (ARR_ACCESS, Var arr, idx_exp), rhs)) ->
        let sub_lhs = BinEx (ARR_ACCESS, Var arr, (sub_vars vals idx_exp)) in
        let new_lhs = replace_arr sub_lhs in
        let new_rhs = replace_arr (sub_vars vals rhs) in
        let v = get_var new_lhs in
        Hashtbl.replace vals v#id new_rhs;
        path_cons

    | Expr (_, BinEx (ASGN, Var v, rhs)) ->
        let new_rhs = replace_arr (sub_vars vals rhs) in
        Hashtbl.replace vals v#id new_rhs;
        path_cons

    | Expr (_, e) ->
        let ne =
            try sub_vars vals (replace_arr (sub_vars vals e))
            with SymbExec_error s ->
            begin
                printf "The troublesome path is:\n";
                List.iter (fun s -> printf "  %s\n" (stmt_s s)) stmts;
                raise (SymbExec_error (s ^ " in: " ^ (expr_s e)))
            end
        in
        if is_c_true path_cons
        then ne
        else BinEx (AND, path_cons, ne)

    | _ -> path_cons
    in
    let add_input v =
        Hashtbl.add vals v#id (Var (get_input sym_tab v))
    in
    let all_vars = List.map (fun (_, s) -> s#as_var) sym_tab#get_symbs_rec in
    let vars = List.filter not_input all_vars in
    List.iter add_input vars;

    let path_cons = List.fold_left exec (Const 1) stmts in
    let path_cons = compute_consts path_cons in
    let is_sat = (not (is_c_false path_cons))
        || ((is_c_true path_cons) && (is_sat solver type_tab path_cons))
    in
    (* XXX: the following code is a disaster, rewrite *)
    let is_hidden = has_hidden_precond sym_tab hidden path_cons in

    if is_final && is_sat && not is_hidden
    then begin
        print_path log;
        let path_cons =
            compute_consts (abstract_hidden sym_tab hidden path_cons) in
        let path_s =
            if not (is_c_true path_cons)
            then Nusmv.expr_s next_fun path_cons
            else ""
        in
        let find_changes (unchanged, changed) v =
            let exp = 
                try Hashtbl.find vals v#id
                with Not_found ->
                    raise (SymbExec_error (sprintf "%s not found" v#qual_name))
            in
            match exp with
            | Var arg ->
                let oarg = get_output sym_tab arg in
                if oarg#id = v#id
                then (v :: unchanged), changed
                else (unchanged, (next_fun v, arg#mangled_name) :: changed)
            | _ ->
                (unchanged, (next_fun v, Nusmv.expr_s next_fun exp) :: changed)
        in
        (* nusmv syntax *)
        activate_hidden sym_tab hidden vals;
        let unchanged, changed = List.fold_left find_changes ([], []) shared in
        let eqs = List.map (fun (v, e) -> sprintf "%s = %s" v e) changed in
        let unchanged = List.filter
            (fun v -> not (List.exists (fun h -> h#id = v#id) hidden)) unchanged
        in
        let unchanged_eqs =
            let mk_eq v = 
                sprintf "next(%s) = %s" v#mangled_name v#mangled_name in
            let mk_init v =
                sprintf "%s = %s" v#mangled_name
                    (Nusmv.type_default_smv (type_tab#get_type v))
            in
            if is_init
            then List.map mk_init unchanged
            else List.map mk_eq unchanged
        in
        let eq_s = if eqs <> [] then "  " ^ (str_join " & " eqs) else ""
        in
        let unchg_s =
            if unchanged <> []
            then "  " ^ (str_join " & " (List.filter (fun s -> s <> "") unchanged_eqs))
            else ""
        in
        let strs = List.filter (fun s -> s <> "") [path_s; eq_s; unchg_s] in
        let expr_s = str_join " & " strs in
        fprintf log " | (%s)\n" expr_s
    end;
    is_sat && not is_hidden

