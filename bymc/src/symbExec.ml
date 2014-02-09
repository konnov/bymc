(*
 * Executing a path symbolically and collecting the constraints
 * along it.
 *
 * The code was tuned to a NuSMV encoding, which was later deprecated.
 * It needs refactoring.
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
    let n = v#get_name in
    let l = String.length n in
    l > 3 && (String.sub n (l - 3) 3) = "_in"

let not_input (v: var): bool = not (is_input v)

let mk_input_name (v: var): string =
    v#get_name ^ "_in"

let mk_output_name (v: var): string =
    let n = v#get_name in
    if is_input v
    then String.sub n 1 ((String.length n) - 1)
    else v#get_name

let get_input (sym_tab: symb_tab) (v: var): var =
    let name = v#get_name ^ "_in" in
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


let path_cnt = ref 0 (* DEBUGGING, remove it afterwards *)
let print_path log path_cons =
    fprintf log "-- PATH %d\n" !path_cnt;
    fprintf log " -> %s\n" (expr_s path_cons);
    if (!path_cnt mod 1000) = 0
    then begin
        printf " visited %d paths...\n" !path_cnt;
        flush stdout;
    end;
    path_cnt := !path_cnt + 1


let exec_path solver log (type_tab: data_type_tab) (sym_tab: symb_tab)
        (shared: var list)
        (path: token basic_block list) (is_final: bool) =
    let vals = Hashtbl.create 10 in
    let stmts = linearize_blocks path in
    (* please, no arrays here *)
    let exec path_cons = function
    | Expr (_, BinEx (ASGN, Var v, rhs)) ->
        let new_rhs = sub_vars vals rhs in
        Hashtbl.replace vals v#id new_rhs;
        path_cons

    | Assume (_, e)
    | Expr (_, e) ->
        let ne =
            try sub_vars vals e
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
        printf " -->>>> %s\n" v#get_name;
        Hashtbl.add vals v#id (Var (get_input sym_tab v))
    in
    let all_vars = List.map (fun s -> s#as_var)
        (List.filter (fun s -> s#get_sym_type = SymVar) sym_tab#get_symbs_rec)
    in
    let vars = List.filter not_input all_vars in
    List.iter add_input vars;

    let path_cons =
        compute_consts(List.fold_left exec (Const 1) stmts) in
    let is_sat = check_sat solver type_tab path_cons in

    if is_final && is_sat
    then begin
        print_path log path_cons
    end;
    is_sat

