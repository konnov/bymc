(**
 
 An improvement of SlpsChecker that generates schemas on-the-fly and supports LTL(F,G).

 Igor Konnov, 2016
 *)

open Batteries
open BatPrintf

open Accums
open Debug
open PorBounds
open SymbSkel
open Poset
open SchemaSmt
open Spin
open SpinIr

exception IllegalLtl_error of string

(* The initial state and the state where the loop starts
   have fixed indices in the partial order.
 *)
let po_init = 1
let po_loop = 0

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


(**
 A classification of temporal formulas
 *)
type spec_t =
    | Safety of Spin.token SpinIr.expr * Spin.token SpinIr.expr
        (* a safety violation: init_form -> F bad_form *)
    | UTL of utl_spec_t
        (* a UTL formula *)


(**
 Find the propositional subformulas that are not covered by a temporal operator.
 *)
let find_uncovered_utl_props form =
    let rec collect col = function
    | TL_p prop ->
        prop :: col

    | TL_and fs ->
        List.fold_left collect col fs

    | _ -> (* skip the temporal operators *)
        col
    in
    collect [] form


(**
 Find the propositional subformulas that are covered by G (as constructed by utl_to_expr).
 *)
let find_G_props form =
    let rec collect col = function
    | TL_G f ->
        (find_uncovered_utl_props f) @ col

    | TL_and fs ->
        List.fold_left collect col fs

    | _ -> (* skip the temporal operators *)
        col
    in
    collect [] form


(**
 Find the propositional subformulas that are not covered by a temporal operator
 in an LTL formula. Similar to find_uncovered_utl_props, but works for LTL, not UTL.
 *)
let keep_uncovered_ltl_props form =
    (* a special expression denoting a deleted subexpression *)
    let deleted = IntConst (-1) in
    let fuse op l r =
        if l = deleted
        then r
        else if r = deleted
            then l
            else BinEx (op, l, r)
    in
    (* remove everything but the propositional formulas *)
    let rec keep = function
    | BinEx(EQ, _, _)
    | BinEx(NE, _, _)
    | BinEx(LT, _, _)
    | BinEx(LE, _, _)
    | BinEx(GT, _, _)
    | BinEx(GE, _, _) as exp ->
        exp

    | UnEx (NEG, exp) ->
        UnEx (NEG, keep exp)

    | BinEx (AND, l, r) ->
        fuse AND (keep l) (keep r)

    | BinEx (OR, l, r) ->
        fuse OR (keep l) (keep r)

    | BinEx (IMPLIES, l, r) ->
        fuse IMPLIES (keep l) (keep r)

    | UnEx (EVENTUALLY, _)
    | UnEx (ALWAYS, _)
    | UnEx (NEXT, _) ->         (* although we do not support nexttime *)
        deleted

    | BinEx (UNTIL, _, _)       (* nor until and release *)
    | BinEx (RELEASE, _, _) ->
        deleted

    | _ as e ->
        raise (Failure ("Unexpected formula: " ^ (SpinIrImp.expr_s e)))
    in
    let res = keep form in
    if res = deleted
    then IntConst 1 (* just true *)
    else res


let find_temporal_subformulas form =
    let rec collect col = function
    | TL_F _ as f ->
        f :: col

    | TL_G _ as f ->
        f :: col

    | TL_and fs ->
        List.fold_left collect col fs

    | _ -> (* skip the propositional subformulas *)
        col
    in
    collect [] form


let atomic_to_expr sk ae =
    let eq0 i =
        BinEx (EQ, Var (SymbSkel.Sk.locvar sk i), IntConst 0)
    in
    let ne0 i =
        BinEx (NE, Var (SymbSkel.Sk.locvar sk i), IntConst 0)
    in
    match ae with
    | And_Keq0 is ->
        list_to_binex AND (List.map eq0 is)

    | AndOr_Kne0 ors ->
        let mk_or is = list_to_binex OR (List.map ne0 is) in
        list_to_binex AND (List.map mk_or ors)


let utl_to_expr sk form =
    let rec trans = function
    | TL_p ae ->
        (atomic_to_expr sk) ae

    | TL_F f ->
        UnEx (EVENTUALLY, trans f)

    | TL_G f ->
        UnEx (ALWAYS, trans f)

    | TL_and fs ->
        list_to_binex AND (List.map trans fs)
    in
    trans form


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


(**
 The elements of the constructed partial order
 *)
type po_elem_t =
    | PO_init of utl_spec_t (** the initial state and the associated formulas *)
    | PO_loop_start         (** the loop start point *)
    | PO_guard of PSet.elt  (** an unlocking/locking guard *)
    | PO_tl of utl_spec_t   (** an extremal appearance of a temporal-logic formula *)


let po_elem_s sk = function
    | PO_guard e ->
        sprintf "G%s" (PSet.elem_str e)

    | PO_tl form ->
        sprintf "TL(%s)" (SpinIrImp.expr_s (utl_to_expr sk form))

    | PO_loop_start ->
        "LOOP"

    | PO_init form ->
        sprintf "INIT(%s)" (SpinIrImp.expr_s (utl_to_expr sk form))


let po_elem_short_s sk elem =
    let trim s =
        if 10 < (String.length s)
        then (String.sub s 0 10) ^ "..."
        else s
    in
    match elem with
    | PO_guard e ->
        sprintf "G%s" (PSet.elem_str e)

    | PO_tl form ->
        sprintf "TL(%s)" (trim (SpinIrImp.expr_s (utl_to_expr sk form)))

    | PO_loop_start ->
        "LOOP"

    | PO_init form ->
        sprintf "INIT(%s)" (trim (SpinIrImp.expr_s (utl_to_expr sk form)))


let find_schema_multiplier invs =
    let count_disjs n = function
        (* as it follows from the analysis, we need 3 * |Disjs| + 1 *)
    | AndOr_Kne0 disjs -> n + (List.length disjs)
        (* this conjunction requires less rules, not more *)
    | And_Keq0 _ -> n
    in
    1 + 3 * (List.fold_left count_disjs 0 invs)


let check_one_order solver sk spec deps tac elem_order =
    let is_safety, safety_init, safety_bad =
        (* we have to treat safety differently from the general case *)
        match spec with
        | Safety (init, bad) -> true, init, bad
        | UTL _ -> false, IntConst 1, IntConst 0 
    in
    let node_type tl =
        if tl = [] then SchemaSmt.Leaf else SchemaSmt.Intermediate
    in
    let assert_propositions invs =
        tac#assert_top (List.map (atomic_to_expr sk) invs)
    in
    let check_steady_schema uset lset invs =
        (* push all the unlocked rules *)
        let push_rule r =
            tac#push_rule deps sk r;
            if invs <> [] then assert_propositions invs
        in
        (* TODO: inefficient, filter out those rules that violate /\ k_i = 0 *)
        let push_schema _ =
            List.iter push_rule (get_unlocked_rules sk deps uset lset)
        in
        (* specifications /\_{X \subseteq Y} \/_{i \in X} k_i \ne 0
           require a schema multiplied several times *)
        BatEnum.iter push_schema (1--(find_schema_multiplier invs));
        let fname = ref "" in
        let on_error frame_hist =
            fname := (SchemaChecker.get_counterex solver sk "fixme" frame_hist) (* FIXME *)
        in
        (* check, whether a safety property is violated *)
        if is_safety
        then if tac#check_property safety_bad on_error
            then { m_is_err_found = true; m_counterexample_filename = !fname }
            else { m_is_err_found = false; m_counterexample_filename = "" }
        else { m_is_err_found = false; m_counterexample_filename = "" }
    in
    let rec search loop_frame uset lset invs = function
        | [] ->
            if is_safety
            (* no errors: we have already checked the prefix *)
            then { m_is_err_found = false; m_counterexample_filename = "" }
            else begin
                tac#assert_frame_eq sk (get_some loop_frame);
                let fname = ref "" in
                let on_error frame_hist =
                    (* FIXME *)
                    fname := (SchemaChecker.get_counterex solver sk "fixme" frame_hist)
                in
                if tac#check_property (IntConst 1) on_error
                then { m_is_err_found = true; m_counterexample_filename = !fname }
                else { m_is_err_found = false; m_counterexample_filename = "" }
            end

        | (PO_init utl_form) :: tl ->
            (* treat the initial state *)
            tac#enter_context;
            if not is_safety
            then assert_propositions (find_uncovered_utl_props utl_form)
            else if not (SpinIr.is_c_true safety_init)
                then tac#assert_top [safety_init];
                
            let new_invs = find_G_props utl_form in
            assert_propositions new_invs;
            let result =
                prune_or_continue loop_frame uset lset (new_invs @ invs) (node_type tl) tl in
            tac#leave_context;
            result

        | (PO_guard id) :: tl ->
            (* An unlocking/locking guard:
               activate the context, check a schema and continue.
               This can be done only outside a loop.
             *)
            if loop_frame = None
            then begin
                let is_unlocking = PSet.mem id deps.D.umask in
                let cond_expr = PSetEltMap.find id deps.D.cond_map in
                tac#enter_context;
                (* fire a sequence of rules that should unlock the condition associated with id *)
                (* XXX: just one rule must fire, otherwise an invariant can be violated! *)
                (get_unlocked_rules sk deps uset lset) |> List.iter (tac#push_rule deps sk) ;
                (* assert that the condition is now unlocked (resp. locked) *)
                tac#assert_top [cond_expr];
                assert_propositions invs;   (* don't forget the invariants *)
                let new_uset, new_lset =
                    if is_unlocking
                    then (PSet.add id uset), lset
                    else uset, (PSet.add id lset)
                in
                let result =
                    prune_or_continue loop_frame new_uset new_lset invs (node_type tl) tl in
                tac#leave_context;
                result
            end else
                search loop_frame uset lset invs tl

        | PO_loop_start :: tl ->
            assert (not is_safety);
            (* TODO: check that no other guards were activated *)
            let loop_start_frame =
                try Some tac#top
                with Failure m ->
                    printf "PO_loop_start: %s\n" m;
                    raise (Failure m)
            in
            prune_or_continue loop_start_frame uset lset invs LoopStart tl

        | (PO_tl (TL_and fs)) :: tl ->
            (* an extreme appearance of F *)
            let props = find_uncovered_utl_props (TL_and fs) in
            tac#enter_context;
            (* the propositional subformulas should be satisfied right now *)
            tac#assert_top (List.map (atomic_to_expr sk) props);
            let new_invs = find_G_props (TL_and fs) in
            let result =
                prune_or_continue loop_frame uset lset (new_invs @ invs) (node_type tl) tl
            in
            tac#leave_context;
            result

        | _ ->
            raise (Failure "Not implemented yet")
    and prune_or_continue loop_frame uset lset invs node_type seq =
        if solver#check
        then begin
            (* try to find an execution
                that does not enable new conditions and reaches a bad state *)
            tac#enter_node node_type;
            let res = fail_first
                (lazy (check_steady_schema uset lset invs))
                (lazy (search loop_frame uset lset invs seq))
            in
            tac#leave_node node_type;
            res
        end else (* the current frame is unreachable *)
            { m_is_err_found = false; m_counterexample_filename = "" }
    in
    (* evaluate the order *)
    if is_safety
    then begin
        let first = List.hd elem_order in
        assert (first = PO_loop_start);
        search None PSet.empty PSet.empty [] (List.tl elem_order) (* prune the loop *)
    end
        else search None PSet.empty PSet.empty [] elem_order


(**
 Add all partial orders induced by the unlocking/locking guards.
 *)
let poset_mixin_guards deps start_pos prec_order rev_map =
    let uconds = deps.D.uconds and lconds = deps.D.lconds in
    let all_ids = List.map (fun (_, id, _, _) -> id) (uconds @ lconds) in
    (* rename the condition ids to the range 0 .. nconds - 1 *)
    let assign_num (n, map) id = (n + 1, PSetEltMap.add id n map) in
    let end_pos, enum_map = List.fold_left assign_num (start_pos, PSetEltMap.empty) all_ids in
    let get_num id =
        try PSetEltMap.find id enum_map
        with Not_found ->
            raise (Failure "Not_found in poset_mixin_guards")
    in
    let new_rev_map =
        PSetEltMap.fold (fun k v m -> IntMap.add v (PO_guard k) m) enum_map rev_map in

    (* construct the partial order *)
    let add_implications a_id implications lst =
        (* b should come before a, as a implies b *)
        let add_impl orders b_id =
            if not (PSet.elem_eq a_id b_id) && PSet.mem b_id implications
            then (get_num b_id, get_num a_id) :: orders
            else orders
        in
        List.fold_left add_impl lst all_ids
    in
    let impl_order = PSetEltMap.fold add_implications deps.D.cond_imp [] in
    let after_init lst i = (po_init, i) :: lst in
    let new_order =
        List.fold_left after_init impl_order (range start_pos end_pos) in
     end_pos, new_order @ prec_order, new_rev_map


(**
 Add all partial orders induced by the unary temporal logic.
 *)
let poset_make_utl form =
    (* positions 1 and 0 correspond to the initial state
       and the start of the loop respectively *)
    let add_form pos form map =
        if IntMap.mem pos map
        then IntMap.add pos (form :: (IntMap.find pos map)) map
        else IntMap.add pos [form] map
    in
    let rec make in_loop (pos, orders, map) = function
    | TL_p _ as e ->
        pos, orders, (add_form pos e map)

    | TL_and fs ->
        List.fold_left (make in_loop) (pos, orders, map) fs

    | TL_G psi ->
        let props = List.map (fun ae -> TL_p ae) (find_uncovered_utl_props psi) in
        let nm = add_form pos (TL_G (TL_and props)) map in
        (* all subformulas should be also true in the loop part *)
        make true (pos, orders, nm) psi

    | TL_F psi ->
        let new_orders =
            if in_loop
            (* pos + 1 must be in the loop *)
            then (po_loop, pos + 1) :: (pos, pos + 1) :: orders
            (* pos + 1 comes after pos *)
            else (pos, pos + 1) :: orders
        in
        make in_loop (pos + 1, new_orders, map) psi
    in
    let n, orders, map = make false (po_init, [], IntMap.empty) form in
    let remap i fs =
        if i = po_init
        then PO_init (TL_and fs)
        else PO_tl (TL_and fs)
    in
    n, orders, (IntMap.mapi remap map)


(**
  Construct the schema tree and check it on-the-fly.

  The construction is similar to compute_static_schema_tree, but is dynamic.
 *)
let gen_and_check_schemas_on_the_fly solver sk spec deps tac =
    let nelems, order, rev_map =
        match spec with
        | UTL utl_form ->
            (* add all the F-formulas to the poset *)
            let n, o, m = poset_make_utl utl_form in
            1 + n, ((po_init, po_loop) :: o), (IntMap.add po_loop PO_loop_start m)

        | Safety (_, _) ->
            (* add the initial state and the loop (the loop will be ignored) *)
            let inite = PO_init (TL_and []) in (* safety is handled explicitely *)
            (* hack: place po_loop BEFORE po_init, so the loop start does not explode
               the number of combinations *)
            2, [(po_loop, po_init)],
                (IntMap.add po_loop PO_loop_start (IntMap.singleton po_init inite))
    in
    (* add the guards *)
    let size, order, rev_map = poset_mixin_guards deps nelems order rev_map in
    let get_elem num =
        try IntMap.find num rev_map
        with Not_found ->
            raise (Failure 
                (sprintf "Not_found (key=%d) in gen_and_check_schemas_on_the_fly" num))
    in
    let pord (a, b) =
        sprintf "%s < %s" (po_elem_s sk (get_elem a)) (po_elem_s sk (get_elem b))
    in
    logtm INFO (sprintf "The partial order is:\n    %s\n\n"
        (str_join ", " (List.map pord order)));
    let ppord (a, b) = sprintf "%d < %d" a b in
    Debug.ltrace Trc.scl
        (lazy (sprintf "The partial order is:\n    %s\n\n"
            (str_join ", " (List.map ppord order))));
    (* enumerate all the linear extensions *)
    let result = ref { m_is_err_found = false; m_counterexample_filename = "" } in
    let iter = linord_iter_first size order in
    while not (linord_iter_is_end iter) && not !result.m_is_err_found do
        let order = BatArray.to_list (linord_iter_get iter) in
        let elem_order = List.map get_elem order in
        let pp e = sprintf "%6s" (po_elem_short_s sk e) in
        printf "  -> %s...\n" (str_join "  " (List.map pp elem_order));
        result := check_one_order solver sk spec deps tac elem_order;
        if not !result.m_is_err_found
        then linord_iter_next iter;
    done;
    !result


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

let extract_utl sk exp =
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
            begin
                try TL_p (atomic_ext_to_atomic (collect_prop f))
                with TemporalOp_found ->
                    raise (IllegalLtl_error
                        ("Unexpected OR with a temporal operator inside: "
                            ^ (SpinIrImp.expr_s f)))
            end

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
    transform (Ltl.normalize_form exp)


let extract_safety_or_utl type_tab sk = function
    (* !(p -> [] q) *)
    | BinEx (AND, lhs, UnEx (EVENTUALLY, rhs)) as f ->
        if (Ltl.is_propositional type_tab lhs)
            && (Ltl.is_propositional type_tab rhs)
        then Safety (Ltl.normalize_form lhs, Ltl.normalize_form rhs)
        else UTL (extract_utl sk f)

    (* !([] q) *)
    | UnEx (EVENTUALLY, sub) as f ->
        if (Ltl.is_propositional type_tab sub)
        then Safety (IntConst 1, Ltl.normalize_form sub)
        else UTL (extract_utl sk f)

    | _ as f ->
        UTL (extract_utl sk f)


let can_handle_spec type_tab sk form =
    try
        ignore (extract_safety_or_utl type_tab sk form);
        true
    with IllegalLtl_error _ ->
        false


let find_error rt tt sk form_name ltl_form deps =
    let check_trivial = function
    | Safety (init_form, bad_form) ->
        if SpinIr.is_c_false bad_form
        then raise (Failure
            (sprintf "%s: bad condition is trivially false" form_name));
        if SpinIr.is_c_false init_form
        then raise (Failure
            (sprintf "%s: initial condition is trivially false" form_name));

    | _ -> ()
    in
    let neg_form = Ltl.normalize_form (UnEx (NEG, ltl_form)) in
    Debug.ltrace Trc.scl
        (lazy (sprintf "neg_form = %s\n" (SpinIrImp.expr_s neg_form)));
    let spec = extract_safety_or_utl tt sk neg_form in
    check_trivial spec;

    rt#solver#push_ctx;
    rt#solver#set_need_model true;

    let ntt = tt#copy in
    let tac = new SchemaChecker.tree_tac_t rt ntt in
    let initf = F.init_frame ntt sk in
    tac#push_frame initf;
    rt#solver#comment "initial constraints from the spec";
    tac#assert_top sk.Sk.inits;

    let result = gen_and_check_schemas_on_the_fly rt#solver sk spec deps tac in
    rt#solver#set_need_model false;
    rt#solver#pop_ctx;
    result

