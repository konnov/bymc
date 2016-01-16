open Printf

open Accums
open SpinTypes
open Spin
open SpinIr
open SpinIrImp
open Debug

exception Ltl_error of string
exception Fairness_error of string
exception Prop_error of string

type spec_t = 
    (* (p && <> !q) *)
    | CondSafety of token expr (* p *) * token expr (* q *)
    | CondGeneral of token expr


let is_propositional type_tab e =
    let rec isp = function
    | Var v -> (type_tab#get_type v)#basetype = TPROPOSITION
    | BinEx(GT, _, _)
    | BinEx(GE, _, _)
    | BinEx(LT, _, _)
    | BinEx(LE, _, _)
    | BinEx(EQ, _, _)
    | BinEx(NE, _, _)
    | BinEx(AT, _, _)
    | LabelRef (_, _) -> true
    | BinEx(AND, l, r) -> (isp l) && (isp r)
    | BinEx(OR, l, r) -> (isp l) && (isp r)
    | BinEx(IMPLIES, l, r) -> (isp l) && (isp r)
    | BinEx(EQUIV, l, r) -> (isp l) && (isp r)
    | BinEx(UNTIL, _, _) -> false
    | BinEx(RELEASE, _, _) -> false
    | BinEx(WEAK_UNTIL, _, _) -> false
    | UnEx(NEG, a) -> isp a
    | UnEx(ALWAYS, _) -> false
    | UnEx(EVENTUALLY, _) -> false
    | UnEx(NEXT, _) -> false
    | _ as e -> raise (Ltl_error ("Not an LTL formula: " ^ (expr_s e)))
    in
    isp e
;;

let normalize_form form =
    let rec norm neg = function
        | Var _ as f -> if neg then UnEx(NEG, f) else f
        | IntConst _ as f -> f
        | BinEx(GT, l, r) as f -> if neg then BinEx(LE, l, r) else f
        | BinEx(GE, l, r) as f -> if neg then BinEx(LT, l, r) else f
        | BinEx(LT, l, r) as f -> if neg then BinEx(GE, l, r) else f
        | BinEx(LE, l, r) as f -> if neg then BinEx(GT, l, r) else f
        | BinEx(EQ, l, r) as f -> if neg then BinEx(NE, l, r) else f
        | BinEx(NE, l, r) as f -> if neg then BinEx(EQ, l, r) else f
        | BinEx(AND, l, r) ->
                if neg
                then BinEx(OR, (norm neg l), (norm neg r))
                else BinEx(AND, (norm neg l), (norm neg r))

        | BinEx(OR, l, r) ->
                if neg
                then BinEx(AND, (norm neg l), (norm neg r))
                else BinEx(OR, (norm neg l), (norm neg r))

        | UnEx(NEG, a) ->
                norm (not neg) a

        | BinEx(IMPLIES, l, r) ->
                if neg
                then BinEx(AND, norm false l, norm true r)
                else BinEx(IMPLIES, norm false l, norm false r)

        | BinEx(EQUIV, l, r) ->
                BinEx(EQUIV, norm neg l, norm neg r)

        | UnEx (EVENTUALLY as t, l)
        | UnEx (ALWAYS as t, l) ->
            let nop = if t = EVENTUALLY then ALWAYS else EVENTUALLY in
            UnEx ((if neg then nop else t), norm neg l)

        | BinEx (UNTIL, l, r) as e ->
            if neg
            then BinEx (RELEASE, norm neg r, norm neg l)
            else e

        | BinEx (RELEASE, r, l) as e ->
            if neg
            then BinEx (UNTIL, norm neg l, norm neg r)
            else e

        (* although we are not using nexttime, its negation is awesome *)
        | UnEx (NEXT, l) ->
            UnEx (NEXT, norm neg l)
        
        | _ as f ->
                let m = (sprintf "Unsupported temporal formula: %s" (expr_s f))
                in
                raise (Ltl_error m)
    in
    norm false form


let classify_spec type_tab = function
    (* (p -> [] q) *)
    | BinEx (IMPLIES, lhs, UnEx (ALWAYS, rhs)) as e ->
        if (is_propositional type_tab lhs)
            && (is_propositional type_tab rhs)
        then CondSafety (lhs, normalize_form (UnEx (NEG, rhs)))
        else CondGeneral e

    (* [] p *)
    | UnEx (ALWAYS, rhs) as e ->
        if is_propositional type_tab rhs
        then CondSafety (IntConst 1, normalize_form (UnEx (NEG, rhs)))
        else CondGeneral e

    (* p || [] q *)
    | BinEx (OR, lhs, UnEx (ALWAYS, rhs)) as e ->
        if (is_propositional type_tab lhs)
            && (is_propositional type_tab rhs)
        then CondSafety (normalize_form (UnEx (NEG, lhs)),
                         normalize_form (UnEx (NEG, rhs)))
        else CondGeneral e

    | e -> CondGeneral e


let embed_atomics type_tab aprops form =
    let get_atomic name =
        try
            match Accums.StringMap.find name aprops with
            | PropGlob e -> e
            | _ ->
                fprintf stderr "WARN: skipped atomic expression: %s\n" name;
                IntConst 1
        with Not_found ->
            raise (Ltl_error ("Atomic expr not found: " ^ name))
    in
    let rec embed = function
        | BinEx(op, l, r) -> BinEx(op, embed l, embed r)
        | UnEx(op, r) -> UnEx(op, embed r)
        | Var v as e ->
            if (type_tab#get_type v)#basetype = SpinTypes.TPROPOSITION
            then embed (get_atomic v#get_name)
            else e
        | _ as e -> e
    in
    embed form


let find_fair_atoms error_fun type_tab aprops = function
    | UnEx(ALWAYS, UnEx(EVENTUALLY, f)) as ff ->
        if is_propositional type_tab f
        then normalize_form (embed_atomics type_tab aprops f)
        else error_fun ff
    | UnEx(EVENTUALLY, UnEx(ALWAYS, f)) as ff ->
        if is_propositional type_tab f
        then normalize_form (embed_atomics type_tab aprops f)
        else error_fun ff
    | _ as ff -> error_fun ff


let is_fairness_form name = str_starts_with "fairness" name 


let collect_fairness_forms ltl_forms =
    (* break down boolean combinations of formulas into a list *)
    let rec collect lst = function
    | BinEx (AND, l, r) ->
            collect (collect lst l) r
    | BinEx (OR, _, _) as f ->
            let m = ("f||g is not supported in fairness: " ^ (expr_s f)) in
            raise (Fairness_error m)
    | BinEx (IMPLIES, _, _) as f ->
            let m = ("f->g is not supported in fairness: " ^ (expr_s f)) in
            raise (Fairness_error m)
    | BinEx (EQUIV, _, _) as f ->
            let m = ("f<->g is not supported in fairness: " ^ (expr_s f)) in
            raise (Fairness_error m)
    | UnEx (NEG, _) as f -> 
            let m = ("!f is not supported in fairness (please normalize): "
                ^ (expr_s f)) in
            raise (Fairness_error m)
    | _ as f -> f :: lst
    in
    let is_ff (name, _) = is_fairness_form name in
    let fforms = List.map (fun (_, f) -> f)
        (List.filter is_ff (hashtbl_as_list ltl_forms)) in
    List.fold_left collect [] fforms


let embed_fairness prog = 
    let ltl_forms = Program.get_ltl_forms_as_hash prog in
    let fairness = list_to_binex AND (collect_fairness_forms ltl_forms) in
    let embed map (name, form) =
        Accums.StringMap.add name (BinEx (IMPLIES, fairness, form)) map in
    let other_fs = List.filter
        (fun (n, _) -> not (is_fairness_form n)) (hashtbl_as_list ltl_forms) in
    let new_forms = List.fold_left embed Accums.StringMap.empty other_fs in
    (Program.set_ltl_forms new_forms prog)


let is_invariant_atomic name =
    Str.string_match (Str.regexp ".*_inv") name 0


let find_invariants (aprops: Spin.token atomic_expr Accums.StringMap.t):
        Spin.token expr list =
    let collect_invariants name prop inv_props =
        let form = match prop with
        | PropGlob e -> e
        | _ ->
            let m = "An invariant must be a glob property: " ^ name in
            raise (Prop_error m)
        in
        if is_invariant_atomic name then form :: inv_props else inv_props
    in
    Accums.StringMap.fold collect_invariants aprops []


let find_proc_name ?err_not_found:(complain=false) e =
    let rec fnd = function
    | Var v -> v#proc_name
    | LabelRef (proc_name, _) -> proc_name
    | BinEx (_, l, r) ->
            let ln, rn = fnd l, fnd r in
            if ln <> rn && ln <> "" && rn <> ""
            then let m = (sprintf "2 procs in one property: %s <> %s" ln rn)
            in raise (Failure m)
            else if ln <> "" then ln else rn
    | UnEx (_, l) -> fnd l
    | _ -> ""
    in
    let name = fnd e in
    if name = "" && complain
    then raise (Failure ("No process name in property: " ^ (expr_s e)))
    else name

