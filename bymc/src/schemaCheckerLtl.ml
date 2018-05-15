(**
 
 An improvement of SchemaChecker that generates schemas on-the-fly
 and supports LTL(F,G) over atomic propositions of constrained form.

 Igor Konnov, 2016
 *)

open Batteries
open Printf

open Mpi (* TODO: extract MPI code into a separate module *)

open Accums
open Debug
open PorBounds
open SymbSkel
open Poset
open SchemaSmt
open Spin
open SpinIr
open SymbSkel

exception IllegalLtl_error of string

(**
 Default filename for a counterexample file
 *)
let cex_default_scm_filename = "cex-fixme.scm"

(* The initial state and the state where the loop starts
   have fixed indices in the partial order.
 *)
let po_init = 1
let po_loop = 0

(* we precompute the number of schemas for use experience,
   but when there are too many, we just say 'too many' *)
let linext_too_many = 100000

(**
 The statistics collected during the execution.
 *)
type stat_t = {
    m_nschemas: int;  (** the number of inspected schemas *)
    m_npred_schemas: int;  (** the number of predicted schemas *)
    m_min_schema_len: int;  (** the minimal schema length encountered *)
    m_max_schema_len: int;  (** the maximal schema length encountered *)
    m_sum_schema_len: int;  (** the sum of all schema lengths (for the average) *)
    m_min_schema_time_sec: float;  (** the minimal time to check a schema *)
    m_max_schema_time_sec: float;  (** the maximum time to check a schema *)
    m_sum_schema_time_sec: float;  (** the sum of all schema times (for the average) *)

    (* internal stats *)
    m_reachopt_sec: float;    (** the time spent with the reachability optimization on *)
    m_noreachopt_sec: float;  (** the time spent with the reachability optimization off *)
    m_reachopt_rounds: int;    (** rounds spent with the reachability optimization on *)
    m_noreachopt_rounds: int;  (** rounds spent with the reachability optimization off *)
    m_nrounds_to_switch: int; (** the number of rounds left before trying to adapt   *)
    m_reachability_on: bool;  (** is the reachability optimization on *)
}

(**
 The record type of a result returned by check_schema_tree_on_the_fly.
 *)
type result_t = {
    m_is_err_found: bool;
    m_counterexample_filename: string;
    m_stat: stat_t;
}

(** Create the initial statistics *)
let mk_stat () =
    let adapt_after =
        if SchemaOpt.is_adaptive_reach_opt_enabled ()
        then SchemaOpt.get_ada_reach_adapt_after ()
        else -1
    in
    {
        m_npred_schemas = 0; m_nschemas = 0;
        m_min_schema_len = max_int; m_max_schema_len = 0;
        m_sum_schema_len = 0; m_min_schema_time_sec = max_float;
        m_max_schema_time_sec = 0.0; m_sum_schema_time_sec = 0.0;
        m_reachopt_sec = 0.0; m_noreachopt_sec = 0.0;
        m_reachopt_rounds = 1; m_noreachopt_rounds = 1;
        m_nrounds_to_switch = adapt_after;
        m_reachability_on = SchemaOpt.is_reach_opt_enabled ();
    }

(** Get the statistics as a string*)
let stat_s st =
    let buf = BatBuffer.create 100 in
    BatBuffer.add_string buf
        (sprintf ("nschemas = %d, min length = %d, max length = %d, avg length = %d\n")
            st.m_nschemas st.m_min_schema_len st.m_max_schema_len
            (st.m_sum_schema_len / st.m_nschemas));
    BatBuffer.add_string buf
        (sprintf "min time = %f, max time = %f, avg time = %f"
            st.m_min_schema_time_sec st.m_max_schema_time_sec
            (st.m_sum_schema_time_sec /. (float_of_int st.m_nschemas)));
    BatBuffer.contents buf


(**
 The type of atomic formulas supported by the model checker
 *)
type atomic_spec_t =
    | And_Keq0 of int list          (** /\_{i \in X} k_i = 0 *)
    | AndOr_Kne0 of int list list   (** /\_{X_j \in Y} \/_{i \in X_j} k_i \ne 0 *)
    | Shared_Or_And_Keq0 of Spin.token SpinIr.expr * int list
                                    (** f(g) \/ /\_{i \in X} k_i = 0 *)


(**
 LTL(F, G) formulas as supported by the model checker
 *)
type utl_k_spec_t =
    | TL_p of atomic_spec_t     (** a conjunction of atomic formulas *)
    | TL_F of utl_k_spec_t        (** F \phi *)
    | TL_G of utl_k_spec_t        (** G \phi *)
    | TL_and of utl_k_spec_t list (* a conjunction *)


(**
 A classification of temporal formulas
 *)
type spec_t =
    | Propositional of Spin.token SpinIr.expr
        (** a purely propositional formula *)
    | Safety of Spin.token SpinIr.expr * Spin.token SpinIr.expr
        (** a safety violation: init_form -> F bad_form *)
    | UTL of Spin.token SpinIr.expr * utl_k_spec_t
        (** an unrestricted formula for the initial state and a UTL formula *)


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
 Find the propositional subformulas that are covered by G (as constructed by utl_k_to_expr).
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
    | BinEx(GE, _, _) as expr ->
        expr

    | UnEx (NEG, exp) ->
        let ke = keep exp in
        if ke = deleted
        then deleted
        else UnEx (NEG, ke)

    | BinEx (AND, l, r) ->
        fuse AND (keep l) (keep r)

    | BinEx (OR, l, r) ->
        fuse OR (keep l) (keep r)

    | BinEx (IMPLIES, l, r) ->
        fuse OR (keep (UnEx (NEG, l))) (keep r)

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
    else Ltl.normalize_form res


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
    (*let varexp i = Var (SymbSkel.Sk.locvar sk i) in*)
    (* We have two choices here: either using boolean expressions
       over tests for zero, or using sums. These two different encodings
       have different performance and memory consumption.
    *)
    match ae with
    | And_Keq0 is ->
        list_to_binex AND (List.map eq0 is)
        (* NOTE: using arithmetics directly
        BinEx (EQ,
            IntConst 0,
            list_to_binex PLUS (List.map varexp is))
         *)

    | AndOr_Kne0 ors ->
        let mk_or is = list_to_binex OR (List.map ne0 is) in
        list_to_binex AND (List.map mk_or ors)
        (* NOTE: using arithmetics directly
        let mk_or is =
            BinEx (LT,
                IntConst 0,
                list_to_binex PLUS (List.map varexp is))
        in
        list_to_binex AND (List.map mk_or ors)
        *)


    | Shared_Or_And_Keq0 (e, is) ->
        BinEx (OR, e, list_to_binex AND (List.map eq0 is))
        (* NOTE: using arithmetics directly
        let rhs =
            BinEx (EQ, IntConst 0, list_to_binex PLUS (List.map varexp is))
        in
        BinEx (OR, e, rhs)
        *)


let utl_k_to_expr sk form =
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


let utl_k_s sk form =
    SpinIrImp.expr_s (utl_k_to_expr sk form)


(** print only temporal operators *)
let rec utl_k_temporal_s = function
    | TL_p _ ->
            "(..)"
    | TL_F f ->
            "F (" ^ (utl_k_temporal_s f) ^ ")"
    | TL_G f ->
            "G (" ^ (utl_k_temporal_s f) ^ ")"
    | TL_and fs ->
            "(" ^ (str_join " /\\ " (List.map utl_k_temporal_s fs)) ^ ")"


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

    | Shared_Or_And_Keq0 (e, is) ->
        let p i = sprintf "k[%d] = 0" i in
        let iss = str_join " /\\ " (List.map p is) in
        sprintf "(%s) \\/ (%s)" (SpinIrImp.expr_s e) iss


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


(** evaluation result *)
type eval_res_t = RTrue | RFalse | RUnknown


(**
 Given the unlocked and locked conditions, propagate the known constants
 within an expression.
 *)
let propagate_conditions sk deps uset lset root =
    let find_value exp =
        let eval_cond res (_, id, cond, lt) =
            if res <> RUnknown
            then res
            else let set = (if lt = Lock then uset else lset) in
                let inv r = (if lt = Unlock then r else not r) in
                if exp = cond
                then if inv (PSet.mem id set) then RTrue else RFalse
                else RUnknown
        in
        List.fold_left eval_cond RUnknown deps.D.uconds
            |> flip (List.fold_left eval_cond) deps.D.lconds
    in
    let of_eval_res e = function
        | RTrue -> IntConst 1
        | RFalse -> IntConst 0
        | RUnknown -> e
    in
    let rec prop = function
    | BinEx (GT, _, _)
    | BinEx (LE, _, _) as e ->
        of_eval_res e (find_value e)

    | BinEx (LT, l, r) as e ->
        of_eval_res e (find_value (BinEx (GT, r, l)))

    | BinEx (GE, l, r) as e ->
        of_eval_res e (find_value (BinEx (LE, r, l)))

    | BinEx (tok, l, r) ->
        BinEx (tok, prop l, prop r)

    | UnEx (tok, e) ->
        UnEx (tok, prop e)

    | _ as e -> e
    in
    prop root


(**
 Get the rules that are unlocked with respect the unlocked/locked conditions.
 *)
let get_unlocked_rules sk deps uset lset invs =
    (* collect those locations
       that are required to be always zero by the invariants *)
    let collect_invs zerolocs = function
        | And_Keq0 is ->
            List.fold_left (flip IntSet.add) zerolocs is

        | _ -> zerolocs
    in
    let zerolocs = List.fold_left collect_invs IntSet.empty invs in
    let collect_enabled lst r no =
        if not (IntSet.mem r.Sk.src zerolocs) && not (IntSet.mem r.Sk.dst zerolocs)
        then no :: lst
        else lst
    in
    let enabled_nos =
        List.fold_left2 collect_enabled [] sk.Sk.rules (range 0 sk.Sk.nrules)
    in
    let unlocked_rule_nos =
        enabled_nos
            |> List.filter (PorBounds.is_rule_unlocked deps uset lset)
            |> PorBounds.pack_rule_set
            
    in
    PorBounds.unpack_rule_set unlocked_rule_nos deps.D.full_segment


(**
 The elements of the constructed partial order
 *)
type po_elem_t =
    | PO_init of utl_k_spec_t (** the initial state and the associated formulas *)
    | PO_loop_start of utl_k_spec_t (** the loop start point (with the invariants) *)
    | PO_guard of PSet.elt  (** an unlocking/locking guard *)
    | PO_tl of int (* id *) * utl_k_spec_t
        (** an extremal appearance of a temporal-logic formula *)


let po_elem_s sk = function
    | PO_guard e ->
        sprintf "C%s" (PSet.elem_str e)

    | PO_tl (id, form) ->
        sprintf "F%d(%s)" id (SpinIrImp.expr_s (utl_k_to_expr sk form))

    | PO_loop_start form ->
        sprintf "LOOP(%s)" (SpinIrImp.expr_s (utl_k_to_expr sk form))


    | PO_init form ->
        sprintf "INIT(%s)" (SpinIrImp.expr_s (utl_k_to_expr sk form))


let po_elem_short_s sk = function
    | PO_guard e ->
        sprintf "C%s" (PSet.elem_str e)

    | PO_tl (id, _) ->
        sprintf "F%d" id

    | PO_loop_start _->
        "LOOP"

    | PO_init _ ->
        sprintf "INIT"


let struc_of_po_elem = function
    | PO_init _ ->
            C.PO_init_struc

    | PO_loop_start _ ->
            C.PO_loop_start_struc

    | PO_guard _ ->
            C.PO_guard_struc

    | PO_tl _ ->
            C.PO_tl_struc


let find_schema_multiplier invs =
    (* (* the first bound we proved *)
    let count_disjs n = function
        (* as it follows from the analysis, we need 3 * |Disjs| + 1 *)
    | AndOr_Kne0 disjs -> n + (List.length disjs)
        (* this conjunction requires less rules, not more *)
    | And_Keq0 _ -> n
        (* similar *)
    | Shared_Or_And_Keq0 _ -> n
    in
    1 + 3 * (List.fold_left count_disjs 0 invs)
    *)
    (*
    (* a better bound we proved later *)
    let count n = function
    | AndOr_Kne0 disjs -> max n 5
    | Shared_Or_And_Keq0 _ -> max n 3
    (* this conjunction requires less rules, not more *)
    | And_Keq0 _ -> n
    in
    1 + List.fold_left count 0 invs
    *)
    (*
      The best bound so far (Theorem 6.4) formulated in the POPL'17
    *)
    let worst n = function
    | AndOr_Kne0 _ -> max n 1           (* multiplying by 2 = 1 + 1 *)
    | Shared_Or_And_Keq0 _ -> max n 1   (* multiplying by 2 = 1 + 1 *)
    | And_Keq0 _ -> max n 0   (* multiplying by 1 = 1 + 0 *)
    in
    1 + List.fold_left worst 0 invs


let dump_counterex_to_file solver sk deps form_name
        (iorder, po_elem_struc_list) prefix_frames loop_frames =
    (* save the counterexample in a human-readable format *)
    let fname = sprintf "cex-%s.trx" form_name in
    let out = open_out fname in
    fprintf out "----------------\n";
    fprintf out " Counterexample\n";
    fprintf out "----------------\n";
    fprintf out "           \n";
    let prefix_len = SchemaChecker.write_counterex solver sk out prefix_frames
    in
    if loop_frames <> []
    then begin
        fprintf out "\n****** LOOP *******\n";
        ignore (SchemaChecker.write_counterex
            solver sk out loop_frames ~start_no:prefix_len)
    end;
    fprintf out "\n Gute Nacht. Spokoinoy nochi. Laku noch.\n";
    close_out out;
    printf "    > Saved counterexample to %s\n" fname;
    (* save the counterexample in a machine-readable format *)
    (* write in a machine-readable format *)
    let machine_fname = cex_default_scm_filename in
    let cex = SchemaChecker.counterex_of_frame_hist
            solver sk deps form_name iorder (prefix_frames @ loop_frames)
            ~start_no:(List.length prefix_frames)
    in
    SchemaSmt.C.save_cex machine_fname
        { cex with C.f_po_struc = po_elem_struc_list }


(** append the invariant lists while filtering out the duplicates *)
let append_invs invs new_invs =
    let tab = Hashtbl.create ((List.length invs) + (List.length new_invs)) in
    let add spec =
        Hashtbl.replace tab spec 1
    in
    List.iter add invs;
    let add_if lst spec =
        if not (Hashtbl.mem tab spec)
        then begin
            Hashtbl.replace tab spec 1;
            spec :: lst
        end
        else lst
    in
    List.fold_left add_if invs new_invs


(** Check whether a rule can update shared variable *)
let is_rule_non_updating sk rule_no =
    let is_redundant = function
        | BinEx (Spin.EQ, UnEx (Spin.NEXT, Var l), Var r) ->
                l#get_name = r#get_name

        | BinEx (Spin.EQ, Var l, UnEx (Spin.NEXT, Var r)) ->
                l#get_name = r#get_name

        | _ -> false
    in
    let rule = List.nth sk.Sk.rules rule_no in
    List.for_all is_redundant rule.Sk.act


(** Check whether a rule changes its local state *)
let is_rule_non_self_loop sk rule_no =
    let rule = List.nth sk.Sk.rules rule_no in
    rule.Sk.src <> rule.Sk.dst



(* an internal result structure *)
type internal_result_t = { m_is_err: bool; m_schema_len: int; }

(* run the first function and if it does not fail, run the second one *)
let fail_first a b =
    let res = Lazy.force a in
    if res.m_is_err
    then res
    else Lazy.force b


(* there are three types of formulas that can be checked by check_one_order *)
type check_t = CheckPropositional | CheckSafety | CheckUtl    


(*
 BUGFIX-20170628: in our verification case studies, we assumed that threshold
 guards can be linearly ordered, e.g., we considered different case that differ
 in the order of threshold guards. For instance, x >= t + 1 always precedes x >= n-t.
 This assumption allowed us to unlock guards one by one, e.g., x >= t + 1 first
 and x >= n - t. This no longer works in synthesis, as we have guards like
 g1: x >= a * n + b * t and g2: x >= c * n + d * t, which cannot ordered in
 consistently. Requiring that g1 is unlocked while g2 is locked will miss
 a counterexample. To deal with such related guards, we introduce predicates
 for each guard that are evaluated during a context switch.
 *)
let check_one_order solver sk (form_name, spec) deps tac ~reach_opt (iorder, elem_order) =
    let check_type, init_form, safety_bad =
        (* In the incremental mode, we distinguish between safety and the general LTL.
           Thus, for safety we do not enumerate possible orderings of F, but
           check on-the-fly, whether a bad state has been reached. Obviously,
           this requires push and pop, which only exist in the incremental mode.
          *)
        match spec with
        | Safety (init, bad) -> CheckSafety, init, bad

        | UTL (init, _) -> CheckUtl, init, IntConst 0 

        | Propositional init -> CheckPropositional, init, IntConst 0
    in
    let node_type tl =
        if tl = [] then SchemaSmt.Leaf else SchemaSmt.Intermediate
    in
    let assert_propositions uset lset props =
        let propagate = propagate_conditions sk deps uset lset in
        if props <> []
        then tac#assert_top (List.map propagate (List.map (atomic_to_expr sk) props))
    in
    let print_top_frame _ =
        printf " >%d" tac#top.F.no; flush stdout;
    in
    let sum_accel_at_most_one frames =
        let expr =
            list_to_binex PLUS (List.map (fun f -> Var f.F.accel_v) frames) in
        if expr <> Nop "" then BinEx (GE, IntConst 1, expr) else IntConst 1
    in
    (* find the unlocked rules excluding the rules as follows:
        when outside the loop, exclude self-loops;
        when inside the loop, exclude the rules that might change shared variables
     *)
    let find_segment_rules in_loop uset lset invs =
        let filt =
            if in_loop
            then is_rule_non_updating sk
            else is_rule_non_self_loop sk
        in
        get_unlocked_rules sk deps uset lset invs
            |> List.filter filt
    in
    let check_steady_schema in_loop uset lset invs =
        let not_and_keq0 = function
            | And_Keq0 _ -> false
            | _ -> true
        in
        let filtered_invs = List.filter not_and_keq0 invs in
        (* push all the unlocked rules *)
        let push_rule r =
            let rule = List.nth sk.Sk.rules r in
            tac#push_rule sk r;
            (* the invariants And_Keq0 are treated in get_unlocked_rules *)
            if rule.Sk.src <> rule.Sk.dst
            (* if the state is changed, change the invariants again *)
            then assert_propositions uset lset filtered_invs
        in
        let push_schema _ =
            let rules = find_segment_rules in_loop uset lset invs in
            if rules <> [] then begin
                (* push the first rule together with the invariants *)
                tac#push_rule sk (List.hd rules);
                assert_propositions uset lset filtered_invs;
                List.iter push_rule (List.tl rules)
            end
            else solver#comment "warning: empty schema"
        in
        (* specifications /\_{X \subseteq Y} \/_{i \in X} k_i \ne 0
           require a schema multiplied several times *)
        let mult = find_schema_multiplier invs in
        assert (mult >= 1);
        tac#pre_steady;
        BatEnum.iter push_schema (1--mult);
        tac#post_steady;
        let on_error frame_hist =
            let po_elem_struc_list = List.map struc_of_po_elem elem_order in
            dump_counterex_to_file solver sk deps
                form_name (iorder, po_elem_struc_list) frame_hist [];
        in
        print_top_frame ();
        (* check, whether a safety property is violated *)
        if check_type = CheckSafety && tac#check_property safety_bad on_error
        then { m_is_err = true; m_schema_len = tac#top.F.no }
        else { m_is_err = false; m_schema_len = tac#top.F.no }
    in
    let at_least_one_step_made loop_start_frame =
        (* make sure that at least one rule had a non-zero factor *)
        let in_prefix f = (f.F.no < loop_start_frame.F.no) in
        let loop_frames = BatList.drop_while in_prefix tac#frame_hist in
        let pos_factor f = BinEx (GT, Var f.F.accel_v, IntConst 0) in
        (* remove the first frame,
           as its acceleration factor still belongs to the prefix *)
        let es = List.map pos_factor (List.tl loop_frames) in
        if es <> []
        then [list_to_binex OR es]
        else []
    in
    let on_error in_loop frame_hist =
        let prefix, loop =
            BatList.span (fun f -> not (in_loop f)) frame_hist in
        let po_elem_struc_list =
            List.map struc_of_po_elem elem_order in
        dump_counterex_to_file solver sk deps
            form_name (iorder, po_elem_struc_list) prefix loop;
    in
    let rec search prefix_last_frame uset lset invs = function
        | [] ->
            if check_type = CheckSafety
            then (* no errors: we have already checked the prefix *)
                { m_is_err = false; m_schema_len = tac#top.F.no }
            else if check_type = CheckPropositional
            then begin (* check whether the initial state can violate the property *)
                let found_bug = tac#check_property (IntConst 1) (on_error (fun _ -> false)) in
                { m_is_err = found_bug; m_schema_len = tac#top.F.no }
            end else begin
                (* close the loop *)
                let lf = get_some prefix_last_frame in
                let in_loop f = (f.F.no >= lf.F.no) in
                let loop_start_frame = List.find in_loop tac#frame_hist in
                printf " END.\n"; flush stdout;
                (* postpone an expensive check with the closed loop *)
                let found_bug =
                if not (tac#check_property (IntConst 1) (on_error in_loop))
                then false (* no counterex. even without a loopback *)
                else begin
                    (* there is probably a bug: close the loop *)
                    printf "    > Closing the loop: LOOPBACK(%d)\n" loop_start_frame.F.no;
                    flush stdout;
                    (* NOTE: These two constraints are expensive in SMT.
                       Add them when it is absolutely necessary. *)
                    tac#assert_frame_eq sk loop_start_frame;
                    tac#assert_top (at_least_one_step_made loop_start_frame);
                    tac#check_property (IntConst 1) (on_error in_loop)
                end
                in
                { m_is_err = found_bug; m_schema_len = tac#top.F.no }
            end

        | (PO_init utl_form) :: tl ->
            (* treat the initial state *)
            tac#enter_context;
            if check_type = CheckUtl
            then assert_propositions uset lset (find_uncovered_utl_props utl_form);
            if not (SpinIr.is_c_true init_form)
            then tac#assert_top [init_form];
                
            let new_invs = find_G_props utl_form in
            assert_propositions uset lset new_invs;
            let result =
                prune_or_continue prefix_last_frame uset lset
                    (append_invs invs new_invs) (node_type tl) tl in
            tac#leave_context;
            result

        | (PO_guard id) :: tl ->
            assert (check_type != CheckPropositional);
            (* An unlocking/locking guard:
               activate the context, check a schema and continue.
               This can be done only outside a loop.
             *)
            if prefix_last_frame = None
            then begin
                let is_locking = PSet.mem id deps.D.lmask in
                let cond_expr = PSetEltMap.find id deps.D.cond_map in
                tac#enter_context;

                (* assert that the condition is not locked yet.
                   It does not work in some cases (see BUGFIX-20170628) *)
                if not (SchemaOpt.use_guard_predicates ()) && is_locking
                then tac#assert_top [cond_expr];

                (* fire a sequence of rules that should unlock the condition associated with id *)
                let push_rule lst r =
                    tac#push_rule sk r;
                    tac#top :: lst
                in
                let in_loop = (prefix_last_frame <> None) in
                tac#pre_steady;
                let frames = find_segment_rules in_loop uset lset invs
                    |> List.fold_left push_rule [] in
                tac#post_steady;

                (*
                 In the following constraint, we say that at most one rule is executed
                 (by at most one process). Otherwise, a sequence of rules might violate
                 an LTL property, or move too many processes and violate a locking guard,
                 e.g., moving from y = 1 to y = 1000 will violate y < 100. 
                 On the other hand, if we fired exactly one transition, this would block
                 an execution with some guards initially unlocked. E.g., if x >= f and
                 f >= 0, then x >= f can be initially unlocked. We simulate this by
                 executing a prefix with zero acceleration factors.
                 *)
                if not (SchemaOpt.use_guard_predicates ()) && is_locking
                then tac#assert_top [sum_accel_at_most_one frames];

                (* assert that the condition is now unlocked (resp. locked) *)
                (* TODO: check m_guard_predicates *)
                if is_locking
                then tac#assert_top [UnEx (NEG, cond_expr)]
                else tac#assert_top [cond_expr];
                assert_propositions uset lset invs;   (* don't forget the invariants *)
                let new_uset, new_lset =
                    if is_locking
                    then uset, (PSet.add id lset)
                    else (PSet.add id uset), lset
                in
                let result =
                    prune_or_continue prefix_last_frame new_uset new_lset invs (node_type tl) tl in
                tac#leave_context;
                result
            end else
                search prefix_last_frame uset lset invs tl

        | (PO_loop_start (TL_and fs)) :: tl ->
            assert (check_type = CheckUtl);
            (* check that no other guards were activated *)
            let assert_not_active set (_, cond_id, expr, lt) =
                if PSet.mem cond_id set
                then tac#assert_top [if lt = Lock then expr else UnEx (NEG, expr)]
            in
            List.iter (assert_not_active (PSet.diff deps.D.umask uset)) deps.D.uconds;
            List.iter (assert_not_active (PSet.diff deps.D.lmask lset)) deps.D.lconds;
            let new_invs = find_G_props (TL_and fs) in
            (* try to close the loop *)
            let prefix_last_frame =
                try Some tac#top
                with Failure m ->
                    printf "PO_loop_start: %s\n" m;
                    raise (Failure m)
            in
            prune_or_continue prefix_last_frame uset lset
                (append_invs invs new_invs) LoopStart tl

        | (PO_tl (_, (TL_and fs))) :: tl ->
            assert (check_type != CheckPropositional);
            (* an extreme appearance of F *)
            let props = find_uncovered_utl_props (TL_and fs) in
            tac#enter_context;
            (* the propositional subformulas should be satisfied right now *)
            assert_propositions uset lset props;
            let new_invs = find_G_props (TL_and fs) in
            (* TODO: figure out, whether the following optimization
                     does not betray completeness:
            let new_invs =
                if prefix_last_frame = None
                then []
                else find_G_props (TL_and fs) in
            *)

            (* Check reachability of the prefix right here.
               In some cases, it gives us good speed ups.
               However, in the non-incremental mode it may cause an
               incredible slowdown from hours to days,
               e.g., see aba.pml, spec agreement *)
            let no_shortcut =
                if SchemaOpt.is_incremental()
                then (tac#check_property (IntConst 1) (on_error (fun _ -> false)))
                else true
            in
            let result =
                if no_shortcut
                then prune_or_continue prefix_last_frame uset lset
                    (append_invs invs new_invs) (node_type tl) tl
                else (* the property contradicts to all the initial states *) 
                    { m_is_err = false; m_schema_len = tac#top.F.no }
            in
            tac#leave_context;
            result

        | _ ->
            raise (Failure "Unexpected po_elem_t")

    and prune_or_continue prefix_last_frame uset lset invs node_type seq =
        (* the following reachability check does not always improve the situation *)
        let no_shortcut =
            if reach_opt
            then (tac#check_property (IntConst 1) (on_error (fun _ -> false)))
            else true
        in
        if no_shortcut
        then begin
            (* first, extend an execution with a suffix
                that does not enable new conditions *)
            tac#enter_node node_type;
            let in_loop = (prefix_last_frame <> None) in
            let res = fail_first
                (lazy (check_steady_schema in_loop uset lset invs))
                (lazy (search prefix_last_frame uset lset invs seq))
            in
            tac#leave_node node_type;
            res
        end else (* the current frame is unreachable *)
            { m_is_err = false; m_schema_len = tac#top.F.no }
    in
    (* evaluate the order *)
    let result = search None PSet.empty PSet.empty [] elem_order in
    printf "\n"; flush stdout;
    result


(**
 Add all partial orders induced by the unlocking/locking guards.
 *)
let poset_mixin_guards deps start_pos prec_order rev_map =
    let uconds = deps.D.uconds and lconds = deps.D.lconds in
    let all_ids = List.map (fun (_, id, _, _) -> id) (uconds @ lconds) in
    (* rename the condition ids to the range 0 .. nconds - 1 *)
    let assign_num (n, map) id =
        if PSetEltMap.mem id map
        then (n, map) (* a guard can be both unlocking and locking, do not add it twice *)
        else (n + 1, PSetEltMap.add id n map)
    in
    let end_pos, enum_map = List.fold_left assign_num (start_pos, PSetEltMap.empty) all_ids in
    let get_num id =
        try PSetEltMap.find id enum_map
        with Not_found ->
            raise (Failure "Not_found in poset_mixin_guards")
    in
    let add_elem k v m = IntMap.add v (PO_guard k) m in
    let new_rev_map = PSetEltMap.fold add_elem enum_map rev_map
    in
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
    let impl_order = PSetEltMap.fold add_implications deps.D.cond_pred [] in
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
    let last_pos = ref po_init in
    let mk_pos _ =
        last_pos := !last_pos + 1; !last_pos
    in
    let add_empty pos map =
        IntMap.add pos [] map
    in
    let add_form pos form map =
        IntMap.add pos (form :: (IntMap.find pos map)) map
    in
    let rec make in_loop pos (orders, map) = function
    | TL_p _ as e ->
        orders, (add_form pos e map)

    | TL_and fs ->
        List.fold_left (make in_loop pos) (orders, map) fs

    | TL_G psi ->
        let props = List.map (fun ae -> TL_p ae) (find_uncovered_utl_props psi) in
        let gp = TL_G (TL_and props) in
        (* add G formulas starting with the current position,
           as well as to the loop start *)
        let nm = add_form pos gp (add_form po_loop gp map) in
        (* all subformulas should be also true in the loop part *)
        make true pos (orders, nm) psi

    | TL_F psi ->
        let new_pos = mk_pos () in
        let new_orders =
            if in_loop
            (* pos + 1 must be in the loop *)
            then (po_loop, new_pos) :: (pos, new_pos) :: orders
            (* pos + 1 comes after pos *)
            else (pos, new_pos) :: orders
        in
        printf "  %s\n"
            (str_join ", " (List.map (fun (a, b) -> sprintf "(%d, %d)" a b) new_orders));
        make in_loop new_pos (new_orders, (add_empty new_pos map)) psi
    in
    (* find the subformulas and compute the dependencies *)
    let init_map = add_empty po_loop (IntMap.singleton po_init []) in
    let orders, map = make false po_init ([], init_map) form in
    let remap i fs =
        if i = po_loop
        then PO_loop_start (TL_and fs)
        else if i = po_init
            then PO_init (TL_and fs)
            else PO_tl (i, TL_and fs)
    in
    printf "Formula structure: %s\n" (utl_k_temporal_s form);
    !last_pos, orders, (IntMap.mapi remap map)


(**
  Given an element order (the elements come from a small set 0..n),
  we compute the unique fingerprint of the order.
  For the moment, we use just a simple string representation.
  XXX: storing fingerprints slowly becomes a bottleneck in this technique.
  TODO: use a trie on po elements.
  *)
let compute_fingerprint order =
    let buf = BatBuffer.create (3 * (List.length order)) in
    let append is_first i =
        if not is_first
        then BatBuffer.add_char buf '.';
        BatBuffer.add_string buf (sprintf "%x" i);
        false
    in
    ignore (List.fold_left append true order);
    BatBuffer.contents buf


(**
  Iterating over partial orders on threshold-and-cut graphs.
  *)
module POI = struct
    type po_iter_t = {
        loiter: linord_iter_t;
        visited: (string, bool) Hashtbl.t;
        map_fun: int -> po_elem_t;
        po_seq: (int list) ref;
        mapped_seq: (po_elem_t list) ref;
    }

    let trunc_guards_after_loop map_fun order =
        let not_loop e = (e <> po_loop) in
        let not_guard num =
            match map_fun num with
            | PO_guard _ -> false
            | _ -> true
        in
        if po_loop = (List.hd order)
        then List.tl order (* incremental safety *)
        else let prefix, loop = BatList.span not_loop order in
            let floop = List.filter not_guard loop in
            prefix @ floop (* liveness or non-incremental safety *)

    (**
      Create a new iterator using an iterator for posets
     *)
    let iter_first map_fun init_linorder_iter =
        let iorder = 
            if linord_iter_is_end init_linorder_iter
            then []
            else trunc_guards_after_loop map_fun
                     (BatArray.to_list (linord_iter_get init_linorder_iter))
        in
        let visited = Hashtbl.create 1024 in
        Hashtbl.add visited (compute_fingerprint iorder) true;
        {
            loiter = init_linorder_iter;
            visited = visited;
            map_fun = map_fun;
            po_seq = ref iorder;
            mapped_seq = ref (List.map map_fun iorder);
        }

    (** Get the current sequence pointed by the iterator *)
    let iter_get_iorder poi =
        !(poi.po_seq)

    (** Get the mapping of the current sequence on po_elem_t *)
    let iter_get_eorder poi =
        !(poi.mapped_seq)

    (** Is the end of the sequence reached? *)
    let iter_is_end poi =
        linord_iter_is_end poi.loiter

    (**
      Advance the iterator value (by updating its arguments in place).
     *)
    let iter_next poi =
        let rec find_next () =
            linord_iter_next poi.loiter;
            if not (linord_iter_is_end poi.loiter)
            then begin
                let order = BatArray.to_list (linord_iter_get poi.loiter) in
                let filtered = trunc_guards_after_loop poi.map_fun order in
                let fingerprint = compute_fingerprint filtered in
                if Hashtbl.mem poi.visited fingerprint
                then find_next ()
                else begin
                    Hashtbl.add poi.visited fingerprint true;
                    poi.po_seq := filtered;
                    poi.mapped_seq := List.map poi.map_fun filtered
                end
            end
        in
        find_next ()
end


(**
  Search iterator.
 *)
module SchemaIter = struct
    type search_iter_t = {
        po_iter: POI.po_iter_t; (** the current iterator on partial orders *)
        err_found: bool;    (** is error found at the current iteration *)
        cex: string option; (** the name of a counterexample (if any) *)
        r_stat: stat_t ref;       (** search statistics *)
    }

    let iter_first po_iter r_stat =
        {
            po_iter; err_found = false; cex = None; r_stat = r_stat;
        }

    let iter_is_end iter =
        POI.iter_is_end iter.po_iter

    let iter_next iter =
        POI.iter_next iter.po_iter;
        { iter with
            err_found = false;
            cex = None;
        }

    let iter_is_err_found iter =
        iter.err_found

    let iter_get_cex iter =
        if iter.err_found
        then get_some iter.cex
        else raise (Failure "No counterexample when iter_is_err_found = false")

    let iter_get_stat iter =
        !(iter.r_stat)

    let set_error iter counterexample_name =
        { iter with err_found = true; cex = Some counterexample_name }
end


(**
  The search structure.
  *)
module S = struct
    (**
     This record type is used to control the search
     *)
    type search_t = {
        iter: SchemaIter.search_iter_t;
            (** the search iterator *)
        check_fun: SchemaIter.search_iter_t -> SchemaIter.search_iter_t;
            (** check the current schema *)
        dispose_search_fun: unit -> unit;
            (** call this function in the end of the search,
                e.g., stop the SMT solver *)
    }
end


let enum_orders (map_fun: int -> po_elem_t)
        (order_fun: (int list * po_elem_t list) -> 'r)
        (is_end_fun: 'r -> bool) (result: 'r ref) (iter: linord_iter_t): 'r =
    let visited = Hashtbl.create 1024 in
    let not_loop e = (e <> po_loop) in
    let not_guard num =
        match map_fun num with
        | PO_guard _ -> false
        | _ -> true
    in
    let filter_guards_after_loop order =
        if po_loop = (List.hd order)
        then List.tl order (* incremental safety *)
        else let prefix, loop = BatList.span not_loop order in
            let floop = List.filter not_guard loop in
            prefix @ floop (* liveness or non-incremental safety *)
    in
    while not (linord_iter_is_end iter) && not (is_end_fun !result) do
        let order = BatArray.to_list (linord_iter_get iter) in
        let filtered = filter_guards_after_loop order in
        let fingerprint = compute_fingerprint filtered in
        if not (Hashtbl.mem visited fingerprint)
        then begin
            (*printf "  visiting %s\n" fingerprint;*)
            Hashtbl.add visited fingerprint true;
            let eorder = List.map map_fun filtered in
            result := order_fun (filtered, eorder);
        end;
        if not (is_end_fun !result)
        then linord_iter_next iter;
    done;
    !result


(** accumulate the statistics and adaptively change the options *)
let accum_stat r_st watch no schema_len =
    let nschemas = !r_st.m_npred_schemas in
    let elapsed, one_lap = watch#next_event "" in
    let eta =
        if no < nschemas
        then elapsed *. (float_of_int (nschemas - no))
            /. (float_of_int no)
        else 0.0
    in
    let percentage = 100 * no / nschemas in
    if nschemas < linext_too_many
    then printf "  %3d%%, lap: %s, elapsed: %s, ETA: %s, nr: %d\n"
        percentage (human_readable_duration one_lap)
        (human_readable_duration elapsed) (human_readable_duration eta) no
    else printf "  (?)%%, lap: %s, elapsed: %s, ETA: unknown, nr: %d\n"
        (human_readable_duration one_lap)
        (human_readable_duration elapsed) no;
            

    (* update the running time with the reachability optimization on/off *)
    let fadd_if is_true a b = if is_true then a +. b else a in
    let add_if is_true a b = if is_true then a + b else a in
    let reach_on = !r_st.m_reachability_on in
    r_st := { !r_st with
        m_nschemas = 1 + !r_st.m_nschemas;
        m_reachopt_sec = fadd_if reach_on !r_st.m_reachopt_sec one_lap;
        m_noreachopt_sec = fadd_if (not reach_on) !r_st.m_noreachopt_sec one_lap;
        m_reachopt_rounds = add_if reach_on !r_st.m_reachopt_rounds 1;
        m_noreachopt_rounds = add_if (not reach_on) !r_st.m_noreachopt_rounds 1;
    };

    let ron_avg = (!r_st.m_reachopt_sec) /. (float_of_int !r_st.m_reachopt_rounds) in
    let roff_avg = (!r_st.m_noreachopt_sec) /. (float_of_int !r_st.m_noreachopt_rounds) in
    let shall_switch =
        ((reach_on && ron_avg > 1.2 *. roff_avg)
            || (not reach_on && roff_avg > 1.2 *. ron_avg))
        && SchemaOpt.is_adaptive_reach_opt_enabled ()
        && SchemaOpt.is_reach_opt_enabled ()
    in
    if !r_st.m_nrounds_to_switch = 0 && shall_switch
    then begin
        r_st := { !r_st with
            m_nrounds_to_switch = SchemaOpt.get_ada_reach_adapt_after ();
            m_reachability_on = not !r_st.m_reachability_on
        };
        printf "Adapting... the reachability optimization is now %s\n"
            (if !r_st.m_reachability_on then "on" else "off");
    end;

    r_st := { !r_st with
        m_min_schema_len = min !r_st.m_min_schema_len schema_len;
        m_max_schema_len = max !r_st.m_max_schema_len schema_len;
        m_min_schema_time_sec = min !r_st.m_min_schema_time_sec one_lap;
        m_max_schema_time_sec = max !r_st.m_max_schema_time_sec one_lap;
        m_sum_schema_len = !r_st.m_sum_schema_len + schema_len;
        m_sum_schema_time_sec = !r_st.m_sum_schema_time_sec +. one_lap;
        m_nrounds_to_switch =
            add_if (!r_st.m_nrounds_to_switch > 0) !r_st.m_nrounds_to_switch (-1);
    }


(**
  Create a cut graph from a UTL_TB formula and add a threshold graph.
  *)
let mk_cut_and_threshold_graph sk deps spec =    
    let nelems, order, rmap =
        match spec with
        | UTL (_, utl_form) ->
            (* add all the F-formulas to the poset *)
            let n, o, m = poset_make_utl utl_form in
            Debug.ltrace Trc.scl
                (lazy (IntMap.iter
                    (fun _ e -> printf "%s\n" (po_elem_s sk e)) m; ""));
            1 + n, ((po_init, po_loop) :: o), m

        | Safety (_, _) ->
            (* add the initial state and the loop (the loop will be ignored) *)
            let inite = PO_init (TL_and []) in (* safety is handled explicitly *)
            (* hack: place po_loop BEFORE po_init, so the loop start does not explode
               the number of combinations *)
            2, [(po_loop, po_init)],
                (IntMap.add po_loop (PO_loop_start (TL_and []))
                    (IntMap.singleton po_init inite))

        | Propositional _ ->
            let inite = PO_init (TL_and []) in (* handled explicitly *)
            (* we need just the initial state for a propositional formula *)
            2, [(po_loop, po_init)],
                (IntMap.add po_loop (PO_loop_start (TL_and []))
                    (IntMap.singleton po_init inite))
    in
    (* add the guards *)
    match spec with
    | Propositional _ ->
        (nelems, order, rmap) (* do not mix in the guards, one schema is enough *)

    | _ -> (* mix in the guards to the order induced by the formula *)
        poset_mixin_guards deps nelems order rmap


(**
  Construct the schema tree and check it on-the-fly.

  The construction is similar to compute_static_schema_tree, but is dynamic.
 *)
let mk_schema_iterator solver sk (form_name, spec) deps tac reset_fun =
    let size, order, rev_map = mk_cut_and_threshold_graph sk deps spec in
    let get_elem num =
        try IntMap.find num rev_map
        with Not_found ->
            raise (Failure 
                (sprintf "Not_found (key=%d) in gen_and_check_schemas_on_the_fly" num))
    in
    let ppord (a, b) = sprintf "%d < %d" a b in
    Debug.ltrace Trc.scl
        (lazy (sprintf "The partial order is:\n    %s\n\n"
            (str_join ", " (List.map ppord order))));
    let pord (a, b) =
        sprintf "%s < %s" (po_elem_short_s sk (get_elem a)) (po_elem_short_s sk (get_elem b))
    in
    logtm INFO (sprintf "%s: the partial order is:\n    %s\n\n"
        form_name (str_join ", " (List.map pord order)));

    (* count the linear extensions *)
    logtm INFO (form_name ^ ": counting linear extensions...");
    let poi = POI.iter_first get_elem (linord_iter_first size order) in
    let total_count = ref 0 in
    while not (POI.iter_is_end poi)
            && !total_count < linext_too_many do (* stop when there are too many *)
        total_count := 1 + !total_count;
        POI.iter_next poi
    done;
    let msg = 
        if !total_count < linext_too_many
        then sprintf
            "%s: %d linear extensions to enumerate\n\n" form_name !total_count
        else sprintf
            "%s: more than %d linear extensions to enumerate (disabled prediction)\n\n" form_name linext_too_many
    in
    logtm INFO msg;

    (* and check the properties for each of them *)
    let current = ref 0 in
    let r_stat = ref ({ (mk_stat ()) with m_npred_schemas = !total_count }) in
    (* we need the watch for user experience,
        the precise timing is given at the end *)
    let watch = new Accums.stop_watch ~is_wall:true ~with_children:true in
    watch#start "";
    let check iter =
        let iorder = POI.iter_get_iorder iter.SchemaIter.po_iter in
        let eorder = POI.iter_get_eorder iter.SchemaIter.po_iter in
        let pp e = sprintf "%3s" (po_elem_short_s sk e) in
        printf "  -> %s: %s...\n" form_name (str_join "  " (List.map pp eorder));
        current := 1 + !current;
        let ropt = !r_stat.m_reachability_on in
        let res = check_one_order solver sk (form_name, spec) deps
                tac ~reach_opt:ropt (iorder, eorder) in
        accum_stat r_stat watch !current res.m_schema_len;
        reset_fun ();
        if res.m_is_err
        then SchemaIter.set_error iter "fixme"
        else iter
    in
    let poi = POI.iter_first get_elem (linord_iter_first size order) in
    (* return the check function and the iterator *)
    (check, SchemaIter.iter_first poi r_stat)


(**
 The functions related to the conversion to an utl_k_spec_t formula.
 *)
module TL = struct
    exception Unexpected_err

    (** Subformulas of LTL(F, G, /\) *)
    type utl_sub_t =
        | Utl_F of Spin.token SpinIr.expr (* propositional *) * utl_sub_t list (* temporal *)
        | Utl_G of Spin.token SpinIr.expr (* propositional *) * utl_sub_t list (* temporal *)
    
    (** The top formula *)
    type utl_top_t =
        Spin.token SpinIr.expr (* propositional *) * utl_sub_t list (* temporal *)


    (** An atomic formula according to our grammar *)
    type atomic_ext_t =
        | Eq0 of int                    (* k_i = 0  *)
        | Ne0 of int                    (* k_i ≠ 0 *)
        | ExtOrNe0 of int list          (* ⋁_{i ∈ X} k_i ≠ 0 *)
        | ExtAndEq0 of int list         (* ⋀_{i ∈ X} k_i = 0 *)
        | ExtAndOrNe0 of int list list  (* ⋀_{1 ≤ j ≤ m} ⋁_{i \in X_j} k_i ≠ 0 *)
        | ExtShared_Or_And_Keq0 of Spin.token SpinIr.expr list * int list
                (* e.g., ((x < t + 1) ⋀ (x < n - t)) ⋁ ⋀_{i ∈ X} k_i = 0 *)
        | ExtList of (Spin.token SpinIr.expr list * int list) list
                (* a conjunction of ExtShared_Or_And_Keq0 instances *)


    let rec utl_tab_of_expr = function
        | BinEx (EQ, _, _)
        | BinEx (NE, _, _)
        | BinEx (LT, _, _)
        | BinEx (LE, _, _)
        | BinEx (GT, _, _)
        | BinEx (GE, _, _) as prop ->
            (prop, [])

        | BinEx (OR, l, r) as exp ->
            let (lp, lt) = utl_tab_of_expr l in
            let (rp, rt) = utl_tab_of_expr r in
            if lt <> [] || rt <> []
            then raise (IllegalLtl_error
                ("A disjunction of temporal subformulas is not allowed: "
                    ^ (SpinIrImp.expr_s exp)))
            else begin
                match (lp, rp) with
                | (Nop "", r) -> (r, [])
                | (l, Nop "") -> (l, [])
                | (l, r) -> (BinEx (OR, l, r), [])
            end

        | BinEx (AND, l, r) ->
            let (lp, lt) = utl_tab_of_expr l in
            let (rp, rt) = utl_tab_of_expr r in
            begin
                match (lp, rp) with
                | (Nop "", r) -> (r, lt @ rt)
                | (l, Nop "") -> (l, lt @ rt)
                | (l, r) -> (BinEx (AND, l, r), lt @ rt)
            end

        | UnEx (EVENTUALLY, sub) ->
            let (props, temps) = utl_tab_of_expr sub in
            (Nop "", [Utl_F (props, temps)])

        | UnEx (ALWAYS, sub) ->
            let (props, temps) = utl_tab_of_expr sub in
            (Nop "", [Utl_G (props, temps)])

        | _ as exp ->
            raise (IllegalLtl_error
                ("Unexpected subformula: " ^ (SpinIrImp.expr_s exp)))


    let atomic_ext_to_utl = function
        | Eq0 i ->
            TL_p (And_Keq0 [i])

        | Ne0 i ->
            TL_p (AndOr_Kne0 [[i]])

        | ExtOrNe0 is ->
            TL_p (AndOr_Kne0 [is])

        | ExtAndEq0 is ->
            TL_p (And_Keq0 is)

        | ExtAndOrNe0 ors ->
            TL_p (AndOr_Kne0 ors)

        | ExtShared_Or_And_Keq0 (shared_es, is) ->
            let not_useless e = (e <> (IntConst 0)) in
            let filtered = List.filter not_useless shared_es in
            if filtered <> []
            then TL_p (Shared_Or_And_Keq0 (list_to_binex OR filtered, is))
            else TL_p (And_Keq0 is)

        | ExtList lst ->
            let not_useless e = (e <> (IntConst 0)) in
            let each (es, is) =
                let filtered = List.filter not_useless es in
                if filtered <> []
                then TL_p (Shared_Or_And_Keq0 (list_to_binex OR filtered, is))
                else TL_p (And_Keq0 is)
            in
            TL_and (List.map each lst)


    let merge_or = function
        | (Ne0 i, Ne0 j) ->
            ExtOrNe0 [i; j]

        | (ExtOrNe0 is, Ne0 j) ->
            ExtOrNe0 (j :: is)

        | (Ne0 i, ExtOrNe0 js) ->
            ExtOrNe0 (i :: js)

        | (ExtOrNe0 is, ExtOrNe0 js) ->
            ExtOrNe0 (is @ js)

        | (ExtShared_Or_And_Keq0 (es1, is1),
           ExtShared_Or_And_Keq0 (es2, is2)) ->
            ExtShared_Or_And_Keq0 (es1 @ es2, is1 @ is2)

        | (ExtShared_Or_And_Keq0 (es, is), ExtAndEq0 js) ->
            ExtShared_Or_And_Keq0 (es, is @ js)

        | (ExtAndEq0 js, ExtShared_Or_And_Keq0 (es, is)) ->
            ExtShared_Or_And_Keq0 (es, js @ is)

        | (ExtShared_Or_And_Keq0 (es, is), Eq0 j) ->
            ExtShared_Or_And_Keq0 (es, j :: is)

        | (Eq0 j, ExtShared_Or_And_Keq0 (es, is)) ->
            ExtShared_Or_And_Keq0 (es, j :: is)

        | _ ->
            raise Unexpected_err


    (* lots of rewriting rules *)
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

        | (Ne0 i, Ne0 j) ->
            (* BUGFIX 20171004: a corner case *)
            ExtAndOrNe0 [[i]; [j]]

        | (Ne0 j, ExtOrNe0 is) ->
            ExtAndOrNe0 [[j]; is]

        | (ExtOrNe0 is, Ne0 j) ->
            ExtAndOrNe0 [[j]; is]

        | (Ne0 j, ExtAndOrNe0 ors) ->
            ExtAndOrNe0 ([j] :: ors)

        | (ExtAndOrNe0 ors, Ne0 j) ->
            ExtAndOrNe0 ([j] :: ors)

        | (ExtShared_Or_And_Keq0 (es1, is1),
           ExtShared_Or_And_Keq0 (es2, is2)) ->
                ExtList [(es1, is1); (es2, is2)]

        | (ExtList lst, ExtShared_Or_And_Keq0 (es, is)) ->
                ExtList ((es, is) :: lst)

        | (ExtShared_Or_And_Keq0 (es, is), ExtList lst) ->
                ExtList ((es, is) :: lst)

        | (ExtList lst1, ExtList lst2) ->
                ExtList (lst1 @ lst2)

        (* ...and many special cases *)
        | (ExtShared_Or_And_Keq0 (es1, is1), Eq0 j) ->
                ExtList [(es1, is1); ([IntConst 0], [j])]

        | (Eq0 j, ExtShared_Or_And_Keq0 (es1, is1)) ->
                ExtList [(es1, is1); ([IntConst 0], [j])]

        | (ExtList lst1, Eq0 j) ->
                ExtList (lst1 @ [([IntConst 0], [j])])

        | (Eq0 j, ExtList lst1) ->
                ExtList (([IntConst 0], [j]) :: lst1)

        (* BUGFIX-20171004: two missing cases *)
        | (ExtAndEq0 js, ExtShared_Or_And_Keq0 (es, is)) ->
                ExtList [([IntConst 0], js); (es, is)]

        | (ExtAndEq0 js, ExtList lst) ->
                ExtList (([IntConst 0], js) :: lst)

        | _ ->
            raise Unexpected_err


    (* NOTE: It is kind of a manually written parser... Needs refactoring. *)
    let extract_utl sk form_exp =
        let var_to_int i v map = IntMap.add v#id i map in
        let rev_map = IntMap.fold var_to_int sk.Sk.loc_vars IntMap.empty
        in
        let find_loc v =
            try IntMap.find v#id rev_map
            with Not_found ->
                let m = sprintf "The location for the variable %s (id=%d) is not found"
                    v#get_name v#id
                in
                raise (Failure m)
        in
        let rec parse_props = function
            | BinEx (EQ as op, IntConst 0, Var x)
            | BinEx (NE as op, IntConst 0, Var x)
            | BinEx (EQ as op, Var x, IntConst 0)
            | BinEx (NE as op, Var x, IntConst 0) as cmp ->
                if IntMap.mem x#id rev_map
                then if op = EQ
                    then Eq0 (find_loc x)
                    else Ne0 (find_loc x)
                else if List.exists (fun v -> x#get_name = v#get_name) sk.Sk.shared
                    then ExtShared_Or_And_Keq0 ([cmp], [])
                    else let m =
                        sprintf "Unexpected formula: %s" (SpinIrImp.expr_s cmp) in
                        raise (IllegalLtl_error m)

            (* a comparison against a linear combination of parameters *)
            | BinEx (NE, Var x, e)
            | BinEx (EQ, Var x, e)
            | BinEx (GE, Var x, e)
            | BinEx (LT, Var x, e)
            | BinEx (GT, Var x, e)
            | BinEx (LE, Var x, e)
            (* multiplication by an integer constant is also fine *)
            | BinEx (NE, BinEx (MULT, IntConst _, Var x), e)
            | BinEx (EQ, BinEx (MULT, IntConst _, Var x), e)
            | BinEx (GE, BinEx (MULT, IntConst _, Var x), e)
            | BinEx (LT, BinEx (MULT, IntConst _, Var x), e)
            | BinEx (GT, BinEx (MULT, IntConst _, Var x), e)
            | BinEx (LE, BinEx (MULT, IntConst _, Var x), e) as cmp
                ->
                if SpinIr.expr_exists SpinIr.not_symbolic e
                then let m = sprintf "Unexpected %s in %s"
                        (SpinIrImp.expr_s e) (SpinIrImp.expr_s cmp) in
                    raise (IllegalLtl_error m)
                else if List.exists (fun v -> x#id = v#id) sk.Sk.shared
                    then ExtShared_Or_And_Keq0 ([cmp], [])
                    else let m =
                        sprintf "Unexpected comparison to a location: %s"
                            (SpinIrImp.expr_s cmp) in
                        raise (IllegalLtl_error m)

            (* synthesis: multiplication by a synthesis parameter
               (called an unknown) is also fine *)
            | BinEx (NE, BinEx (MULT, Var u, Var x), e)
            | BinEx (EQ, BinEx (MULT, Var u, Var x), e)
            | BinEx (GE, BinEx (MULT, Var u, Var x), e)
            | BinEx (LT, BinEx (MULT, Var u, Var x), e)
            | BinEx (GT, BinEx (MULT, Var u, Var x), e)
            | BinEx (LE, BinEx (MULT, Var u, Var x), e) as cmp
                ->
                if not (List.mem u sk.Sk.unknowns)
                then let m = sprintf ("A variable should be multiplied by an unknown"
                        ^^ " or an integer constant in %s") (SpinIrImp.expr_s cmp) in
                    raise (IllegalLtl_error m)
                else if SpinIr.expr_exists SpinIr.not_symbolic e
                then let m = sprintf "Unexpected %s in %s"
                        (SpinIrImp.expr_s e) (SpinIrImp.expr_s cmp) in
                    raise (IllegalLtl_error m)
                else if List.exists (fun v -> x#id = v#id) sk.Sk.shared
                    then ExtShared_Or_And_Keq0 ([cmp], [])
                    else let m =
                        sprintf "Unexpected comparison to a location: %s"
                            (SpinIrImp.expr_s cmp) in
                        raise (IllegalLtl_error m)

            | BinEx (OR, l, r) as expr ->
                begin
                    try merge_or (parse_props l, parse_props r)
                    with Unexpected_err ->
                        let m = sprintf "Unexpected %s in %s"
                                (SpinIrImp.expr_s expr) (SpinIrImp.expr_s form_exp) in
                        raise (IllegalLtl_error m)
                end

            | BinEx (AND, l, r) as expr ->
                begin
                    try merge_and (parse_props l, parse_props r)
                    with Unexpected_err ->
                        let m = sprintf "Unexpected %s in %s"
                                (SpinIrImp.expr_s expr) (SpinIrImp.expr_s form_exp) in
                        raise (IllegalLtl_error m)
                end
        
            | _ as e ->
                raise (IllegalLtl_error
                    (sprintf "Expected an and-or combination of counter tests, found %s"
                        (SpinIrImp.expr_s e)))
        in
        let parse_props_p props =
            if props <> Nop ""
            then atomic_ext_to_utl (parse_props props)
            else TL_and []
        in
        let join = function
            | (TL_and [], [f]) -> f
            | (TL_p p, []) -> TL_p p
            | (TL_and [TL_and ls], rs) -> TL_and (ls @ rs)
            | (TL_and ls, rs) -> TL_and (ls @ rs)
            | (l, r) -> TL_and (l :: r)
        in
        let rec parse_tl = function
            | Utl_F (props, temps) ->
                let ps = parse_props_p props in
                let tls = List.map parse_tl temps in
                TL_F (join (ps, tls))

            | Utl_G (props, temps) ->
                let ps = parse_props_p props in
                let tls = List.map parse_tl temps in
                TL_G (join (ps, tls))
        in
        let (props, temps) = utl_tab_of_expr (Ltl.normalize_form form_exp) in
        let tls = List.map parse_tl temps in
        if props = Nop ""
        then (IntConst 1, join (TL_and [], tls))
        else (props, join (TL_and [], tls))
end

let extract_utl = TL.extract_utl


let extract_safety_or_utl type_tab sk = function
    (* !(p -> [] q) *)
    | BinEx (AND, lhs, UnEx (EVENTUALLY, rhs)) as f ->
        if (Ltl.is_propositional type_tab lhs)
            && (Ltl.is_propositional type_tab rhs)
        then Safety (Ltl.normalize_form lhs, Ltl.normalize_form rhs)
        else let ltl, utl = TL.extract_utl sk f in
            UTL (ltl, utl)

    (* !([] q) *)
    | UnEx (EVENTUALLY, sub) as f ->
        if (Ltl.is_propositional type_tab sub)
        then Safety (IntConst 1, Ltl.normalize_form sub)
        else let ltl, utl = TL.extract_utl sk f in
            UTL (ltl, utl)

    | _ as f ->
        let ltl, utl = TL.extract_utl sk f in
            UTL (ltl, utl)


let can_handle_spec type_tab sk form =
    try
        ignore (extract_safety_or_utl type_tab sk form);
        true
    with IllegalLtl_error m ->
        log INFO (sprintf "IllegalLtl_error: %s\n" m);
        false

(**
 * This function enumerates all lassos that can potentially form a counterexample.
 *
 * NOTE: this function creates multiple copies of the SMT solver.
 *)
let mk_search_control rt tt sk form_name ltl_form deps =
    let check_trivial = function
    | Propositional init_form ->
        if SpinIr.is_c_false init_form
        then raise (Failure
            (sprintf "%s: initial condition is trivially false" form_name));

    | Safety (init_form, bad_form) ->
        if SpinIr.is_c_false bad_form
        then raise (Failure
            (sprintf "%s: bad condition is trivially false" form_name));
        if SpinIr.is_c_false init_form
        then raise (Failure
            (sprintf "%s: initial condition is trivially false" form_name));

    | UTL (init_form, _) ->
        if SpinIr.is_c_false init_form
        then raise (Failure
            (sprintf "%s: initial condition is trivially false" form_name));
    in
    let neg_form = Ltl.normalize_form (UnEx (NEG, ltl_form)) in
    Debug.ltrace Trc.scl
        (lazy (sprintf "neg_form = %s\n" (SpinIrImp.expr_s neg_form)));
    let spec =
        if Ltl.is_propositional tt neg_form
        then (* the simplest case: the formula does not have temporal operators *)
            Propositional neg_form
        else if SchemaOpt.is_incremental ()
            (* safety is treated specially in the incremental mode *)
            then extract_safety_or_utl tt sk neg_form
            else let ltl, utl = TL.extract_utl sk neg_form in
                UTL (ltl, utl)
    in
    check_trivial spec;

    (* Create own copy of the solver, instead of corrupting
       the global instance. *)
    let my_solver =
        rt#solver#clone_not_started
        ?logic:(Some "QF_LIA") ("schemaLtl_" ^ form_name) in

    let ntt = tt#copy in
    let tac = new SchemaChecker.tree_tac_t my_solver ntt deps in
    let initf = F.init_frame ntt sk in
    let init_solver_fun _ =
        my_solver#comment "top-level declarations";
        let append_var v = my_solver#append_var_def v (tt#get_type v) in
        List.iter append_var sk.Sk.params;
        let append_expr e = ignore (my_solver#append_expr e) in
        let non_trivial e = e <> (IntConst 1) in
        List.iter append_expr (List.filter non_trivial sk.Sk.assumes);
        (* BUGFIX: erase all frames,
            otherwise we add more and more initial frames*)
        tac#reset;
        tac#push_frame initf;
        my_solver#comment "initial constraints from the spec";
        (* push the initial node, so the predicate optimization works *)
        tac#assert_top sk.Sk.inits;
    in
    let reset_fun _ =
        if not (SchemaOpt.is_incremental ())
        then begin
            (* reset does not work in cvc4 *)
            my_solver#stop;
            my_solver#set_incremental_mode false;
            my_solver#start;
            init_solver_fun ();
        end
    in

    (* WARNING: here we restart the solver *)
    my_solver#start;
    my_solver#set_need_model true;
    tac#set_incremental (SchemaOpt.is_incremental ());
    init_solver_fun ();
    (* enumerate all linear extensions *)
    let (check_fun, iter) =
        mk_schema_iterator my_solver sk (form_name, spec) deps tac reset_fun
    in
    {
        S.iter = iter;
        S.check_fun = check_fun;
        S.dispose_search_fun = (fun _ -> my_solver#stop);
    }


(**
 * This function enumerates all lassos that can potentially form a counterexample.
 *
 * NOTE: this function creates multiple copies of the SMT solver.
 *)
let find_error_in_single_form rt tt sk form_name ltl_form deps =
    let ctrl = mk_search_control rt tt sk form_name ltl_form deps in
    let rec search iter =
        if SchemaIter.iter_is_end iter
        then iter
        else let iter = ctrl.S.check_fun iter in
            if SchemaIter.iter_is_err_found iter
            then iter
            else search (SchemaIter.iter_next iter)
    in
    let end_iter = search ctrl.S.iter in
    ctrl.S.dispose_search_fun ();
    end_iter


(** a search iterator and the accompanying checking function *)
type iterXfun_t =
    SchemaIter.search_iter_t * (SchemaIter.search_iter_t -> SchemaIter.search_iter_t)

(** iteration outcome *)
type outcome_t = Error | NoError | Aborted

(**
  Iterator type for find_error_in_many_forms_interleaved_MPI, similar to S.search_t.
  *)
type inter_iter_t = {
    (* an iteration number *)
    m_iter_no: int;
    (* a list of iterators to be checked *)
    m_iterXfuns: iterXfun_t list;
    (* the search outcome *)
    m_outcome: outcome_t;
}

(** The processing command for the current iteration *)
type iter_cmd_t =
    | CheckAndNext  (* check and continue *)
    | SkipAndNext   (* no checking, just continue *)
    | Abort         (* abort the iteration *)


(** interleave many search iterators until the search is over or aborted *)
let next_inter_iter
        (cmd_fun: int -> iter_cmd_t) (iter: inter_iter_t) : inter_iter_t =
    let iterXfuns =
        List.filter (fun (i, _) -> not (SchemaIter.iter_is_end i)) iter.m_iterXfuns
    in
    let iter_no = iter.m_iter_no in
    (* check a schema for each iterator and abort, if an error is found *)
    let rec map_or_fail = function
    | [] -> (NoError, [])

    | (i, check_fun) :: tl ->
            let (outcome, nis) = map_or_fail tl in
            if outcome = Error || outcome = Aborted
            then (outcome, nis)    (* terminate *)
            else begin
                let cmd = cmd_fun iter_no in
                let ni =
                    if cmd = CheckAndNext
                    then (check_fun i)
                    else i
                in
                let is_err = SchemaIter.iter_is_err_found ni in
                if is_err || cmd = Abort
                then ((if is_err then Error else Aborted), [(ni, check_fun)]) (* error or abort *)
                else (NoError, (SchemaIter.iter_next ni, check_fun) :: nis) (* continue *)
            end
    in
    let (outcome, next_iterXfuns) = map_or_fail iterXfuns in
    {
        m_iter_no = 1 + iter_no;
        m_iterXfuns =
            if outcome = Error || outcome = Aborted
            then [List.last next_iterXfuns] (* there must be one *)
            else next_iterXfuns;
        m_outcome = outcome;
    }


(* A parameterized implementation of
    find_error_in_many_forms_interleaved and find_error_in_many_forms_parallel
    (see below)
 *)
let find_error_in_many_forms_impl
        (cmd_fun: int -> iter_cmd_t) rt tt sk named_forms deps =
    let rec find iter =
        match iter.m_outcome with
        | Aborted ->
                None

        | Error ->
                Some (fst (List.hd iter.m_iterXfuns))

        | NoError ->
            if iter.m_iterXfuns = []
            then None
            else find (next_inter_iter cmd_fun iter)
    in
    let mk_ctrl (name, form) = mk_search_control rt tt sk name form deps in
    let ctrls = List.map mk_ctrl named_forms in
    let iterXfuns = List.map (fun c -> (c.S.iter, c.S.check_fun)) ctrls in
    let init_iter = { m_iter_no = 0; m_iterXfuns = iterXfuns; m_outcome = NoError } in
    let result = find init_iter in
    List.iter (fun c -> c.S.dispose_search_fun ()) ctrls;
    result

(**
   This function is similar to find_error_in_single_form but it enumerates
   lassos for multiple formulas. The lassos that correspond to different
   formulas are interleaved, i.e., the ith lasso of the first formula is
   checked, then the ith lasso of the second formula, etc. The function stops
   when either the first error is found, or all lassos are enumerated.

   If an error is found, then (Some filename) is returned.
   Otherwise None is returned.
 
   NOTE: this function creates multiple copies of the SMT solver.
 *)
let find_error_in_many_forms_interleaved rt tt sk named_forms deps =
    let cmd_fun _ = CheckAndNext in
    match find_error_in_many_forms_impl cmd_fun rt tt sk named_forms deps with
    | None -> None

    | Some iter -> Some (SchemaIter.iter_get_cex iter)


let tag_cex = 2     (* collecting counterexamples *)
let tag_error = 1   (* quick notifications to let other processes know that an error was found *)


(**
    Check many lassos like in find_error_in_many_forms_interleaved,
    but do it in parallel using MPI (the node 0 is used as the root).
    
    TODO: extract this code into a separate module.
 *)
let find_error_in_many_forms_parallel rt tt sk named_forms deps =
    let id = Mpi.comm_rank Mpi.comm_world in
    let npeers = Mpi.comm_size Mpi.comm_world in
    log INFO (sprintf "MPI: node %d out of %d started\n" id npeers);
    let notify j i =
        ignore (Mpi.isend j i tag_error Mpi.comm_world)
    in
    let cmd_fun j =
        let abort =
            (* check whether anybody has sent a quick notification *)
            match Mpi.iprobe Mpi.any_source tag_error Mpi.comm_world with
            | None ->
                    false

            | Some (src, _) ->
                    ignore (Mpi.receive src tag_error Mpi.comm_world);
                    log INFO (sprintf "MPI: node %d notified %d on error. Aborting.\n" src id);
                    if id = 0
                    then begin (* notify the workers *)
                        BatEnum.iter (notify 0) (1--^npeers)
                    end;
                    true
        in
        if abort
        then Abort
        else if (id <> (j mod npeers))
            then SkipAndNext
            else CheckAndNext
    in
    let result =
        find_error_in_many_forms_impl cmd_fun rt tt sk named_forms deps
    in
    log INFO (sprintf "MPI: node %d finished verification.\n" id);
    if result <> None
    then begin
        if id = 0
        then BatEnum.iter (notify 0) (1--^npeers)    (* notify the workers   *)
        else notify id 0                            (* notify the master    *)
    end;
    log INFO (sprintf "MPI: node %d joins the gather.\n" id);
    (* the master gathers the results *)
    let flags = Mpi.gather (result != None) 0 Mpi.comm_world in
    let result =
        if id = 0
        then begin
            try
                let witness = Array.findi (fun b -> b) flags in
                (* error found *)
                log INFO (sprintf "Node %d has found a counterexample\n" witness);
                ignore (Mpi.broadcast witness 0 Mpi.comm_world);
                (* transfer a filename, TODO: transfer a counterexample here *)
                let filename =
                    if witness = 0
                    then SchemaIter.iter_get_cex (get_some result)
                    else begin
                        let cex = Mpi.receive witness tag_cex Mpi.comm_world in
                        (* save the counterexample locally *)
                        C.save_cex cex_default_scm_filename cex;
                        cex_default_scm_filename (* and return the filename *)
                    end
                in
                log INFO (sprintf "Saved counterexample in %s\n" filename);
                Some filename
            with Not_found ->
                ignore (Mpi.broadcast (-1) 0 Mpi.comm_world);
                None (* no error found *)
        end else begin
            let witness = Mpi.broadcast 0 0 Mpi.comm_world in
            if witness = id
            then begin
                let cex = C.load_cex cex_default_scm_filename in
                Mpi.send cex 0 tag_cex Mpi.comm_world;
            end;
            if witness != -1
            then Some (sprintf "CheckNode%d" witness)
            else None
        end
    in
    (* clean the stale notifications and return *)
    let rec clean _ =
        match Mpi.iprobe Mpi.any_source tag_error Mpi.comm_world with
        | None ->
                result

        | Some (src, _) ->
                ignore (Mpi.receive src tag_error Mpi.comm_world);
                clean ()
    in
    clean ()

