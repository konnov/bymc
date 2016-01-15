(**
 
 An improvement of SlpsChecker that generates schemas on-the-fly and supports LTL(F,G).

 Igor Konnov, 2016
 *)

open Batteries
open BatPrintf

open Accums
open PorBounds
open SymbSkel
open Poset
open SchemaSmt
open Spin
open SpinIr

exception IllegalLtl_error of string


(**
 The record type of a result returned by check_schema_tree_on_the_fly.
 *)
type result_t = {
    m_is_err_found: bool;
    m_counterexample_filename: string;
}


(**
 The type of atomic formulas supported by the model checker
 *)
type atomic_spec_t =
    | And_Keq0 of int list          (** /\_{i \in X} k_i = 0 *)
    | AndOr_Kne0 of int list list   (** /\_{X_j \in Y} \/_{i \in X_j} k_i \ne 0 *)


(**
 LTL(F, G) formulas as supported by the model checker
 *)
type utl_spec_t =
    | TL_p of atomic_spec_t     (** a conjunction of atomic formulas *)
    | TL_F of utl_spec_t        (** F \phi *)
    | TL_G of utl_spec_t        (** G \phi *)
    | TL_and of utl_spec_t list (* a conjunction *)


(** Convert an atomic formula to a string *)
let rec atomic_spec_s = function
    | And_Keq0 indices ->
        let p i = sprintf "k[%d] = 0" i in
        sprintf "(%s)" (str_join " /\\ " (List.map p indices))

    | AndOr_Kne0 disjs ->
        let p i = sprintf "k[%d] != 0" i in
        let pd indices =
            sprintf "(%s)" (str_join " \\/ " (List.map p indices))
        in
        sprintf "(%s)" (str_join " /\\ " (List.map pd disjs))


(** Convert a UTL formula to a string *)
let rec utl_spec_s = function
    | TL_p prop ->
        atomic_spec_s prop

    | TL_F form ->
        sprintf "F (%s)" (utl_spec_s form)

    | TL_G form ->
        sprintf "G (%s)" (utl_spec_s form)

    | TL_and forms ->
        sprintf "(%s)" (str_join " /\\ " (List.map utl_spec_s forms))


(* run the first function and if it does not fail, run the second one *)
let fail_first a b =
    let res = Lazy.force a in
    if res.m_is_err_found
    then res
    else Lazy.force b


let get_unlocked_rules sk deps uset lset =
    let unlocked_rule_nos =
        (range 0 sk.Sk.nrules)
            |> List.filter (PorBounds.is_rule_unlocked deps uset lset)
            |> PorBounds.pack_rule_set
            
    in
    PorBounds.unpack_rule_set unlocked_rule_nos deps.D.full_segment


let check_one_order solver sk bad_form deps tac id_order =
    let check_steady_schema uset lset =
        (* push all the unlocked rules *)
        (get_unlocked_rules sk deps uset lset) |> List.iter (tac#push_rule deps sk);
        let fname = ref "" in
        let on_error frame_hist =
            fname := (SchemaChecker.get_counterex solver sk "fixme" frame_hist) (* FIXME *)
        in
        if tac#check_property bad_form on_error
        then { m_is_err_found = true; m_counterexample_filename = !fname }
        else { m_is_err_found = false; m_counterexample_filename = "" }
    in
    let rec search uset lset = function
        | [] ->
            (* no errors: we have already checked the prefix *)
            { m_is_err_found = false; m_counterexample_filename = "" }

        | id :: tl -> (* activate the context, check a schema and go further *)
            let node_type = (if tl = [] then SchemaSmt.Leaf else SchemaSmt.Intermediate) in
            let is_unlocking = PSet.mem id deps.D.umask in
            let cond_expr = PSetEltMap.find id deps.D.cond_map in
            tac#enter_context;
            (* fire a sequence of rule that should unlock the condition associated with id *)
            (get_unlocked_rules sk deps uset lset) |> List.iter (tac#push_rule deps sk) ;
            (* assert that the condition is now unlocked (resp. locked) *)
            tac#assert_top [cond_expr];

            let result =
                if solver#check
                then begin
                    (* try to find an execution
                        that does not enable new conditions and reaches a bad state *)
                    let new_uset, new_lset =
                        if is_unlocking
                        then (PSet.add id uset), lset
                        else uset, (PSet.add id lset)
                    in
                    tac#enter_node node_type;
                    let res = fail_first
                        (lazy (check_steady_schema new_uset new_lset))
                        (lazy (search new_uset new_lset tl))
                    in
                    tac#leave_node node_type;
                    res
                end else (* this frame is unreachable *)
                    { m_is_err_found = false; m_counterexample_filename = "" }
            in
            tac#leave_context;
            result
    in
    (* check the empty context first *)
    let first_type =
        (if id_order = [] then SchemaSmt.Leaf else SchemaSmt.Intermediate) in
    tac#enter_context;
    tac#enter_node first_type;
    let result =
        fail_first
            (lazy (check_steady_schema PSet.empty PSet.empty))
            (lazy (search PSet.empty PSet.empty id_order))
    in
    tac#leave_node first_type;
    tac#leave_context;
    result


(**
  Construct the schema tree and check it on-the-fly.

  The construction is similar to compute_static_schema_tree, but is dynamic.
 *)
let gen_and_check_schemas_on_the_fly solver sk bad_form deps tac =
    let uconds = deps.D.uconds and lconds = deps.D.lconds in
    let all_ids = List.map (fun (_, id, _, _) -> id) (uconds @ lconds) in
    (* rename the condition ids to the range 0 .. nconds - 1 *)
    let assign_num (n, map) id = (n + 1, PSetEltMap.add id n map) in
    let n, enum_map = List.fold_left assign_num (0, PSetEltMap.empty) all_ids in
    let get_num id = PSetEltMap.find id enum_map in
    let rev_map =
        PSetEltMap.fold (fun k v m -> IntMap.add v k m) enum_map IntMap.empty in
    let get_id num = IntMap.find num rev_map in
    (* construct the partial order *)
    let add_orders a_id implications lst =
        (* b should come before a, as a implies b *)
        List.fold_left
            (fun orders b_id ->
                if not (PSet.elem_eq a_id b_id) && PSet.mem b_id implications
                then (get_num b_id, get_num a_id) :: orders
                else orders)
            lst all_ids
    in
    let prec_order = PSetEltMap.fold add_orders deps.D.cond_imp [] in
    let pord (a, b) =
        sprintf "%s < %s" (PSet.elem_str (get_id a)) (PSet.elem_str (get_id b))
    in
    printf "The partial order is:\n    %s\n\n" (str_join ", " (List.map pord prec_order));
    let ppord (a, b) = sprintf "%d < %d" a b in
    Debug.ltrace Trc.scl
        (lazy (sprintf "The partial order is:\n    %s\n\n" (str_join ", " (List.map ppord prec_order))));
    (* enumerate all the linear extensions *)
    let result = ref { m_is_err_found = false; m_counterexample_filename = "" } in
    let iter = linord_iter_first n prec_order in
    while not (linord_iter_is_end iter) && not !result.m_is_err_found do
        let order = BatArray.to_list (linord_iter_get iter) in
        let id_order = List.map get_id order in
        let pp e = sprintf "%3s" (PSet.elem_str e) in
        printf "  -> %s...\n" (str_join "  " (List.map pp id_order));
        result := check_one_order solver sk bad_form deps tac id_order;
        if not !result.m_is_err_found
        then linord_iter_next iter;
    done;
    !result


(* XXX: extend to LTL(F, G) *)
let extract_spec type_tab s =
    match Ltl.classify_spec type_tab s with
    | Ltl.CondSafety (init, bad) -> (init, bad)
    | _ ->
        let m = sprintf "unsupported LTL formula: %s" (SpinIrImp.expr_s s) in
        raise (Ltl.Ltl_error m)


type atomic_ext_t =
    | Eq0 of int
    | Ne0 of int
    | ExtOrNe0 of int list
    | ExtAndEq0 of int list
    | ExtAndOrNe0 of int list list


let atomic_ext_to_atomic = function
    | Eq0 i -> And_Keq0 [i]
    | Ne0 i -> AndOr_Kne0 [[i]]
    | ExtOrNe0 is -> AndOr_Kne0 [is]
    | ExtAndEq0 is -> And_Keq0 is
    | ExtAndOrNe0 ors -> AndOr_Kne0 ors


exception Unexpected_err    

let merge_or = function
    | (Ne0 i, Ne0 j) ->
        ExtOrNe0 [i; j]

    | (ExtOrNe0 is, Ne0 j) ->
        ExtOrNe0 (j :: is)

    | (Ne0 i, ExtOrNe0 js) ->
        ExtOrNe0 (i :: js)

    | (ExtOrNe0 is, ExtOrNe0 js) ->
        ExtOrNe0 (is @ js)

    | _ ->
        raise Unexpected_err


(* an amazing number of combinations *)
let merge_and = function
    | (Eq0 i, Eq0 j) ->
        ExtAndEq0 [i; j]

    | (ExtAndEq0 is, Eq0 j) ->
        ExtAndEq0 (j :: is)

    | (Eq0 j, ExtAndEq0 is) ->
        ExtAndEq0 (j :: is)

    | (ExtAndEq0 is, ExtAndEq0 js) ->
        ExtAndEq0 (is @ js)

    | (ExtOrNe0 is, ExtOrNe0 js) ->
        ExtAndOrNe0 [is; js]

    | (ExtAndOrNe0 ors, ExtAndOrNe0 ors2) ->
        ExtAndOrNe0 (ors @ ors2)

    | (ExtAndOrNe0 ors, ExtOrNe0 js) ->
        ExtAndOrNe0 (js :: ors)

    | (ExtOrNe0 js, ExtAndOrNe0 ors) ->
        ExtAndOrNe0 (js :: ors)

    | (Ne0 j, ExtOrNe0 is) ->
        ExtAndOrNe0 [[j]; is]

    | (ExtOrNe0 is, Ne0 j) ->
        ExtAndOrNe0 [[j]; is]

    | (Ne0 j, ExtAndOrNe0 ors) ->
        ExtAndOrNe0 ([j] :: ors)

    | (ExtAndOrNe0 ors, Ne0 j) ->
        ExtAndOrNe0 ([j] :: ors)

    | _ ->
        raise Unexpected_err


exception TemporalOp_found

let to_utl sk exp =
    let var_to_int i v map =
        IntMap.add v#id i map
    in
    let rev_map = IntMap.fold var_to_int sk.Sk.loc_vars IntMap.empty in
    let rec collect_prop = function
        | BinEx (NE, Var v, IntConst 0) ->
            Ne0 (IntMap.find v#id rev_map)

        | BinEx (EQ, Var v, IntConst 0) ->
            Eq0 (IntMap.find v#id rev_map)

        | BinEx (OR, l, r) as e ->
            begin
                try merge_or (collect_prop l, collect_prop r)
                with Unexpected_err ->
                    let m = sprintf "Unexpected %s in %s"
                            (SpinIrImp.expr_s e) (SpinIrImp.expr_s exp) in
                    raise (IllegalLtl_error m)
            end

        | BinEx (AND, l, r) as e ->
            begin
                try merge_and (collect_prop l, collect_prop r)
                with Unexpected_err ->
                    let m = sprintf "Unexpected %s in %s"
                            (SpinIrImp.expr_s e) (SpinIrImp.expr_s exp) in
                    raise (IllegalLtl_error m)
            end
        
        | UnEx (ALWAYS, _) 
        | UnEx (EVENTUALLY, _)
        | UnEx (NEXT, _)
        | UnEx (UNTIL, _)
        | UnEx (RELEASE, _) ->
            raise TemporalOp_found

        | _ as e ->
            raise (IllegalLtl_error
                (sprintf "Expected an and-or combinations of counter tests, found %s"
                    (SpinIrImp.expr_s e)))
    in
    let rec transform = function
        | BinEx (OR, _, _) as f ->
            TL_p (atomic_ext_to_atomic (collect_prop f))

        | BinEx (EQ, Var _, IntConst 0) as f ->
            TL_p (atomic_ext_to_atomic (collect_prop f))

        | BinEx (NE, Var _, IntConst 0) as f ->
            TL_p (atomic_ext_to_atomic (collect_prop f))

        | UnEx (ALWAYS, e) ->
            TL_G (transform e)

        | UnEx (EVENTUALLY, e) ->
            TL_F (transform e)

        | BinEx (AND, l, r) as f ->
            begin
                try TL_p (atomic_ext_to_atomic (collect_prop f))
                with TemporalOp_found ->
                    TL_and [transform l; transform r]
            end

        | _ as e ->
            raise (IllegalLtl_error
                (sprintf "Unexpected LTL formula: %s" (SpinIrImp.expr_s e)))

    in
    transform exp


let find_error rt tt sk form_name ltl_form deps =
    let init_form, bad_form = extract_spec tt ltl_form in
    if SpinIr.is_c_false bad_form
    then raise (Failure "Bad condition is trivially false");

    rt#solver#push_ctx;
    rt#solver#set_need_model true;

    let ntt = tt#copy in
    let tac = new SchemaChecker.tree_tac_t rt ntt in
    let initf = F.init_frame ntt sk in
    tac#push_frame initf;
    tac#assert_top sk.Sk.inits;
    rt#solver#comment "initial constraints from the spec";
    if SpinIr.is_c_false init_form
    then raise (Failure "Initial condition is trivially false");
    if not (SpinIr.is_c_true init_form)
    then tac#assert_top [init_form];

    let result = gen_and_check_schemas_on_the_fly rt#solver sk bad_form deps tac in
    rt#solver#set_need_model false;
    rt#solver#pop_ctx;
    result

