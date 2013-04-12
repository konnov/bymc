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
    (String.length n) > 0 && (String.get n 0) = 'I'

let not_input (v: var): bool = not (is_input v)

let mk_input_name (v: var): string =
    "I" ^ v#mangled_name

let mk_output_name (v: var): string =
    let n = v#mangled_name in
    if is_input v
    then String.sub n 1 ((String.length n) - 1)
    else v#mangled_name

let get_input (sym_tab: symb_tab) (v: var): var =
    let name = "I" ^ v#mangled_name in
    let sym = sym_tab#lookup name in
    sym#as_var

let get_output (sym_tab: symb_tab) (v: var): var =
    (sym_tab#lookup (mk_output_name v))#as_var

let get_use (sym_tab: symb_tab): var =
    (sym_tab#lookup "bymc_use")#as_var

let get_loc (sym_tab: symb_tab): var =
    (sym_tab#lookup "bymc_loc")#as_var

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


let hide_non_zero sym_tab hidden_idx_fun exp =
    let find_idx v =
        let ov = get_output sym_tab v in
        hidden_idx_fun ov
    in
    let rec rewrite = function
    | BinEx (EQ, Var v, Const i) as e ->
        let idx = find_idx v in
        if i > 0 && idx > 0
        then Const 0 (* FALSE *)
        else e

    | BinEx (NE, Var v, Const i) as e ->
        let idx = find_idx v in
        if i = 0 && idx > 0
        then Const 0 (* FALSE *)
        else e

    | BinEx (EQ, Var v, _)
    | BinEx (NE, Var v, _) as e ->
        let idx = find_idx v in
        if idx > 0
        then begin
            Const 0 (* FALSE *)
        end
        else e

    | BinEx (t, l, r) ->
        BinEx (t, rewrite l, rewrite r)

    | UnEx (t, r) ->
        UnEx (t, rewrite r)

    | _ as e -> e
    in
    compute_consts (rewrite exp)


let abstract_hidden sym_tab hidden_idx_fun vals exp = 
    let rec rewrite = function
    | BinEx (EQ, Var v, _)
    | BinEx (NE, Var v, _) as e ->
        let idx = hidden_idx_fun (get_output sym_tab v) in
        if idx > 0
        then begin
            let use_var = get_use sym_tab in
            (* remember that this transition was hidden *)
            Hashtbl.replace vals use_var#id (Const idx);
            Const 1 (* TRUE *)
        end
        else e

    | BinEx (t, l, r) ->
        BinEx (t, rewrite l, rewrite r)

    | UnEx (t, r) ->
        UnEx (t, rewrite r)

    | _ as e -> e
    in
    compute_consts (rewrite exp)


let activate_hidden sym_tab shared hidden_idx_fun vals =
    let try_activate v =
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
        let use_var = get_use sym_tab in
        if needs_activation
        then begin
            (* activate *)
            Hashtbl.replace vals use_var#id (Const (hidden_idx_fun v));
            (* deactivate *)
            Hashtbl.replace vals v#id (Var (get_input sym_tab v))
        end
    in
    let hidden = List.filter (fun v -> (hidden_idx_fun v) <> 0) shared in 
    List.iter try_activate hidden


let indexed_var v idx = sprintf "%s_%dI" v#mangled_name idx

let smv_name sym_tab v =
    let oname = (get_output sym_tab v)#mangled_name in
    if is_input v
    then oname
    else sprintf "next(%s)" oname


let keep_name v = v#mangled_name


let path_cnt = ref 0 (* DEBUGGING, remove it afterwards *)
let print_path log =        
    fprintf log "-- PATH %d\n" !path_cnt;
    if (!path_cnt mod 1000) = 0
    then begin
        printf " visited %d paths...\n" !path_cnt;
        flush stdout;
    end;
    path_cnt := !path_cnt + 1


let elim_array_access sym_tab exp =
    let rec elim = function
    | BinEx (ARR_ACCESS, Var arr, Const i) ->
        Var ((sym_tab#lookup (indexed_var arr i))#as_var)
    | BinEx (ARR_ACCESS, Var arr, idx_exp) ->
        raise (SymbExec_error
            (sprintf "Expected a constant index, found: %s" (expr_s idx_exp)))
    | BinEx (t, l, r) -> BinEx (t, elim l, elim r)
    | UnEx (t, e) -> UnEx (t, elim e)
    | _ as e -> e
    in
    elim exp


let exec_path solver log (type_tab: data_type_tab) (sym_tab: symb_tab)
        (shared: var list) (hidden_idx_fun: var -> int)
        (name_f: var -> string)
        (is_init: bool)
        (path: token basic_block list) (is_final: bool) =
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
        let new_lhs = elim_array_access sym_tab sub_lhs in
        let new_rhs = elim_array_access sym_tab (sub_vars vals rhs) in
        let v = get_var new_lhs in
        Hashtbl.replace vals v#id new_rhs;
        path_cons

    | Expr (_, BinEx (ASGN, Var v, rhs)) ->
        let new_rhs = elim_array_access sym_tab (sub_vars vals rhs) in
        Hashtbl.replace vals v#id new_rhs;
        path_cons

    | Expr (_, e) ->
        let ne =
            try sub_vars vals (elim_array_access sym_tab (sub_vars vals e))
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
    let is_sat = check_sat solver type_tab path_cons
    in
    (* XXX: the following code is a disaster, rewrite *)
    let hidden_path_cons = hide_non_zero sym_tab hidden_idx_fun path_cons in
    let is_hidden = not (check_sat solver type_tab hidden_path_cons) in

    if is_final && is_sat && not is_hidden
    then begin
        print_path log;
        let path_cons = abstract_hidden sym_tab hidden_idx_fun vals path_cons
        in
        let var_loc = get_loc sym_tab in
        let init_path_cons =
            let init_expr =
                BinEx (EQ, Var (get_input sym_tab var_loc),
                       Const (if is_init then 0 else 1)) in
            if is_c_true path_cons
            then init_expr
            else BinEx (AND, path_cons, init_expr) in
        let path_s = Nusmv.expr_s name_f init_path_cons in
        let find_changes (unchanged, changed) v =
            let exp = 
                try Hashtbl.find vals v#id
                with Not_found ->
                    raise (SymbExec_error (sprintf "%s not found" v#mangled_name))
            in
            match exp with
            | Var arg ->
                let oarg = get_output sym_tab arg in
                if oarg#id = v#id
                then (v :: unchanged), changed
                else (unchanged, (name_f v, arg#mangled_name) :: changed)
            | _ ->
                (unchanged, (name_f v, Nusmv.expr_s name_f exp) :: changed)
        in

        (* the first step is initialization *)
        Hashtbl.add vals var_loc#id (Const 1);
        (* nusmv syntax *)
        activate_hidden sym_tab shared hidden_idx_fun vals;
        let unchanged, changed = List.fold_left find_changes ([], []) shared in
        let eqs = List.map (fun (v, e) -> sprintf "%s = %s" v e) changed in
        let unchanged =
            List.filter (fun v -> (hidden_idx_fun v) = 0) unchanged
        in
        let unchanged_eqs =
            let mk_eq v = 
                sprintf "%s = %s" (name_f (get_output sym_tab v))
                    (name_f (get_input sym_tab v)) in
            List.map mk_eq unchanged
        in
        let eq_s = if eqs <> [] then "  " ^ (str_join " & " eqs) else ""
        in
        let unchg_s =
            if unchanged <> []
            then "  " ^ (str_join " & " (List.filter str_nempty unchanged_eqs))
            else ""
        in
        let strs = List.filter str_nempty [path_s; eq_s; unchg_s] in
        fprintf log " | (%s)\n" (str_join " & " strs)
    end;
    is_sat && not is_hidden

