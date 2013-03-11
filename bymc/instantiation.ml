(*
 * Substitute parameter values and produce standard Promela code.
 *)

open Map
open Printf
module StringMap = Map.Make (String)

open Accums
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

let rec conc_expr pa exp =
    let find_var name =
        try StringMap.find name pa
        with Not_found -> raise (Failure ("Parameter not found: " ^ name))
    in
    match exp with
    | Var v ->
            if not v#is_symbolic
            then Var v
            else 
                let value = find_var v#get_name in
                Const value
    | UnEx (t, l) -> UnEx (t, conc_expr pa l)
    | BinEx (t, l, r) ->
            let sl, sr = conc_expr pa l, conc_expr pa r in
            try_eval (BinEx (t, sl, sr))
    | _ as e -> e

type quant = ForAll | Exist

let conc_prop pa pmap prop = 
    let rec find_proc_name = function
        | Var v -> v#proc_name
        | LabelRef (proc_name, _) -> proc_name
        | BinEx (_, l, r) ->
                let ln, rn = find_proc_name l, find_proc_name r in
                if ln <> rn && ln <> "" && rn <> ""
                then let m = (sprintf "2 procs in one property: %s <> %s" ln rn)
                in raise (Failure m)
                else if ln <> "" then ln else rn
        | UnEx (_, l) -> find_proc_name l
        | _ -> ""
    in
    let rec mk_inst e idx =
        match e with
        | Var v ->
                let name = if v#proc_name = ""
                then v#get_name
                else sprintf "%s[%d]:%s" v#proc_name idx v#get_name in
                Var (v#copy name)
        | LabelRef (proc_name, lab) ->
                LabelRef (sprintf "%s[%d]" proc_name idx, lab)
        | UnEx (tok, l) -> UnEx (tok, mk_inst l idx)
        | BinEx (tok, l, r) -> BinEx (tok, mk_inst l idx, mk_inst r idx)
        | _ -> e
    in
    let find_proc pname =
        try StringMap.find pname pmap
        with Not_found -> raise (Failure ("Process name not found: " ^ pname))
    in
    let rec unfold q = function
        | BinEx (AND, l, r) -> BinEx (AND, unfold q l, unfold q r)
        | BinEx (OR, l, r) -> BinEx (OR, unfold q l, unfold q r)
        | UnEx (NEG, l) -> UnEx (NEG, unfold q l)
        | BinEx (EQ, l, r)
        | BinEx (NE, l, r)
        | BinEx (LE, l, r)
        | BinEx (LT, l, r)
        | BinEx (GE, l, r)
        | BinEx (GT, l, r) as e ->
                let pname = find_proc_name e in
                if pname = ""
                then e (* no process variables inside *)
                else let count = find_proc pname in
                    let clones = List.map (mk_inst e) (range 0 count) in
                    let tok = if q = ForAll then AND else OR in
                    list_to_binex tok clones
        | LabelRef (pname, label) as e ->
                let count = find_proc pname in
                let clones = List.map (mk_inst e) (range 0 count) in
                let tok = if q = ForAll then AND else OR in
                list_to_binex tok clones
        | _ as e -> e
    in
    let rec replace_card = function
        | UnEx (CARD, l) -> Const 0 (* how to do cardinality in the concrete? *)
        | UnEx (t, l) -> UnEx (t, replace_card l)
        | BinEx (t, l, r) -> BinEx (t, replace_card l, replace_card r)
        | _ as e -> e
    in
    let rec tr_ae = function
    | PropAll e ->
        let pname = find_proc_name e in
        if pname = ""
        then PropGlob e (* no process variables inside *)
        else let count = find_proc pname in
            let clones = List.map (mk_inst (conc_expr pa e)) (range 0 count) in
            PropGlob (list_to_binex AND clones)
    | PropSome e ->
        let pname = find_proc_name e in
        if pname = ""
        then PropGlob e (* no process variables inside *)
        else let count = find_proc pname in
            let clones = List.map (mk_inst (conc_expr pa e)) (range 0 count) in
            PropGlob (list_to_binex OR clones)
    | PropGlob e -> PropGlob (conc_expr pa (replace_card e))
    | PropAnd (l, r) -> PropAnd (tr_ae l, tr_ae r)
    | PropOr (l, r) -> PropOr (tr_ae l, tr_ae r)
    in
    tr_ae prop

let rec concretize_stmt pa pmap stmt =
    let find_var name =
        try StringMap.find name pa
        with Not_found -> raise (Failure ("Parameter not found: " ^ name))
    in
    match stmt with
    | MDecl (id, v, e) as d ->
            if v#is_symbolic
            then let n = v#get_name in
                MUnsafe (id, (sprintf "/* %s = %d */" n (find_var n)))
            else d
    | MExpr (id, e) ->
            MExpr (id, conc_expr pa e)
    | MDeclProp (id, v, e) ->
            MDeclProp (id, v, conc_prop pa pmap e)
    | MAssume (id, e) ->
            MUnsafe (id, (sprintf "/* %s */" (expr_s e)))
    | MIf (id, options) ->
            MIf (id, (List.map (conc_opt (concretize_stmt pa pmap)) options))
    | MAtomic (id, seq) ->
            MAtomic (id, (conc_seq (concretize_stmt pa pmap) seq))
    | MD_step (id, seq) ->
            MD_step (id, (conc_seq (concretize_stmt pa pmap) seq))
    | _ as s -> s
and 
    conc_opt cfun = function
        | MOptGuarded seq -> MOptGuarded (conc_seq cfun seq)
        | MOptElse seq -> MOptElse (conc_seq cfun seq)
and
    conc_seq cfun seq = (List.map cfun seq)
;;

let concretize_proc pa pmap p =
    let new_seq = (List.map (concretize_stmt pa pmap) p#get_stmts) in
    let new_p = proc_replace_body p new_seq in
    let count =
        try (StringMap.find p#get_name pmap)
        with Not_found -> raise (Failure ("No process count for " ^ p#get_name))
    in
    new_p#set_active_expr (Const count);
    new_p
;;

let concretize_unit param_vals pmap lmap = function
    | EmptyUnit -> EmptyUnit
    | Ltl (name, form) ->
            let fairness = StringMap.find "fairness" lmap in
            let embedded = BinEx (IMPLIES, fairness, form) in
            if name <> "fairness"
            then begin
                let out = open_out (sprintf "%s.ltl" name) in
                fprintf out "%s\n" (expr_s embedded);
                close_out out
            end;
            EmptyUnit
    | Stmt s ->
            Stmt (concretize_stmt param_vals pmap s)
    | Proc p ->
            Proc (concretize_proc param_vals pmap p)
;;

let do_substitution (param_vals: int StringMap.t)
        (units: 't prog_unit list) : ('t prog_unit list) =
    let count_proc pmap = function
        | Proc p -> 
            let cnt = begin match (conc_expr param_vals p#get_active_expr) with
            | Const i -> i
            | _ as e -> raise (Failure ("Failed to compute: " ^ (expr_s e)))
            end in
            StringMap.add p#get_name cnt pmap
        | _ -> pmap
    in
    let pmap = List.fold_left count_proc StringMap.empty units in
    let collect_ltl fmap = function
        | Ltl (name, form) -> StringMap.add name form fmap
        | _ -> fmap
    in
    let lmap = List.fold_left collect_ltl StringMap.empty units in
    List.map (concretize_unit param_vals pmap lmap) units
;;
