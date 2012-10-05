(*
 * Substitute parameter values and produce standard Promela code.
 *)

open Map
open Printf
module StringMap = Map.Make (String)

open Spin
open SpinIr
open SpinIrImp

let try_eval = function
    | BinEx(PLUS, Const li, Const ri) ->
            Const (li + ri)
    | BinEx(MINUS, Const li, Const ri) ->
            Const (li - ri)
    | BinEx(MULT, Const li, Const ri) ->
            Const (li * ri)
    | BinEx(DIV, Const li, Const ri) ->
            Const (li / ri)
    | _ as e -> e

let rec conc_expr pa = function
    | Var v ->
            if v#is_symbolic then Const (StringMap.find v#get_name pa) else Var v
    | UnEx (t, l) -> UnEx (t, conc_expr pa l)
    | BinEx (t, l, r) ->
            let sl, sr = conc_expr pa l, conc_expr pa r in
            try_eval (BinEx (t, sl, sr))
    | _ as e -> e

let conc_prop pa = function
    | PropAll e -> ...
    | _ as p -> p

let rec concretize_stmt pa = function
    | MDecl (id, v, e) as d ->
            if v#is_symbolic
            then let n = v#get_name in
                MUnsafe (id, (sprintf "/* %s = %d */" n (StringMap.find n pa)))
            else d
    | MExpr (id, e) ->
            MExpr (id, conc_expr pa e)
    | MDeclProp (id, v, e) ->
            MDeclProp (id, v, conc_prop pa e)
    | MAssume (id, e) ->
            MUnsafe (id, (sprintf "/* %s */" (expr_s e)))
    | MIf (id, options) ->
            MIf (id, (List.map (conc_opt pa) options))
    | MAtomic (id, seq) ->
            MAtomic (id, (conc_seq pa seq))
    | MD_step (id, seq) ->
            MD_step (id, (conc_seq pa seq))
    | _ as s -> s
and 
    conc_opt pa = function
        | MOptGuarded seq -> MOptGuarded (conc_seq pa seq)
        | MOptElse seq -> MOptElse (conc_seq pa seq)
and
    conc_seq pa seq = (List.map (concretize_stmt pa) seq)
;;

let concretize_proc pa p =
    let count = match (conc_expr pa p#get_active_expr) with
    | Const i -> i
    | _ as e -> raise (Failure ("Failed to compute: " ^ (expr_s e)))
    in
    let new_p = proc_replace_body p (List.map (concretize_stmt pa) p#get_stmts)
    in
    new_p#set_active_expr (Const count);
    new_p
;;

let concretize_unit param_assignments = function
    | None -> None
    | Ltl (_, _) as e -> e
    | Stmt s -> Stmt (concretize_stmt param_assignments s)
    | Proc p -> Proc (concretize_proc param_assignments p)
;;

let do_substitution (param_assignments: int StringMap.t)
        (units: 't prog_unit list) : ('t prog_unit list) =
    List.map (concretize_unit param_assignments) units
;;
