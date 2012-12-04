(*
  The place where we do counter abstraction w.r.t. interval domain.
  This code was written in an ad-hoc way and requires refactoring.

  Igor Konnov 2012
 *)

open Printf

open Accums
open Spin
open SpinIr
open SpinIrImp
open Smt
open Cfg
open Analysis
open Ssa
open SkelStruc
open CfgSmt
open Debug

open AbsBasics
open VarRole
open AbsInterval
open Refinement
open Regions
open Ltl

open PiaCtrCtx


let mk_nondet_choice = function
(*
if
    :: seq_0;
    :: seq_1;
...
fi
*)
    | [] -> raise (Abstraction_error "An alternative in the empty list")
    | [seq] -> seq
    | seqs -> [MIf (-1, List.map (fun seq -> MOptGuarded seq) seqs)]


let rec remove_bad_statements stmts =
    let pred s =
        match s with
        | MPrint (_, _, _) -> false
        | _ -> true
    in
    let rec rem_s = function
        | MAtomic (id, seq) -> MAtomic (id, remove_bad_statements seq)
        | MD_step (id, seq) -> MD_step (id, remove_bad_statements seq)
        | MIf (id, opts) ->
            let on_opt = function
                | MOptGuarded seq -> MOptGuarded (remove_bad_statements seq)
                | MOptElse seq -> MOptElse (remove_bad_statements seq)
            in
            MIf (id, (List.map on_opt opts))
        | _ as s -> s
    in
    let filter l s = if pred s then (rem_s s) :: l else l in
    List.rev (List.fold_left filter [] stmts)


let trans_prop_decl solver ctr_ctx_tbl prog atomic_expr =
    let mk_cons c_ctx tok sep indices =
        let add_cons e idx =
            let ke = BinEx (ARR_ACCESS, Var c_ctx#get_ctr, Const idx) in
            if is_nop e
            then BinEx (tok, ke, Const 0)
            else BinEx (sep, e, BinEx (tok, ke, Const 0)) in
        List.fold_left add_cons (Nop "") indices
    in
    let mk_all c_ctx check_fun =
        mk_cons c_ctx EQ AND
            (c_ctx#all_indices_for (fun m -> not (check_fun m))) in
    let mk_some c_ctx check_fun =
        mk_cons c_ctx NE OR (c_ctx#all_indices_for check_fun) in
    (* abstract expressions over locals as one boolean function *)
    let rec eval_bool_expr e vals =
        match e with
        | BinEx (EQ, Var var, Const value) ->
            if not (Program.is_global prog var)
            then value = (Hashtbl.find vals var)
            else true (* don't touch global variables *)
        | BinEx (EQ, Const value, Var var) ->
            eval_bool_expr (BinEx (EQ, Var var, Const value)) vals
        | BinEx (NE, Var var, Const value) ->
            if not (Program.is_global prog var)
            then value != (Hashtbl.find vals var)
            else true (* don't touch global variables *)
        | BinEx (NE, Const value, Var var) ->
            eval_bool_expr (BinEx (NE, Var var, Const value)) vals 
        | BinEx (AND, l, r) ->
            (eval_bool_expr l vals) && (eval_bool_expr r vals)
        | BinEx (OR, l, r) ->
            (eval_bool_expr l vals) || (eval_bool_expr r vals)
        | UnEx (NEG, l) ->
            not (eval_bool_expr l vals)
        | _ as e ->
            raise (Abstraction_error
                (sprintf "Don't know how to do counter abstraction for %s"
                    (expr_s e)))
    in
    let is_global = function
    | Var v -> Program.is_global prog v
    | _ -> false
    in
    let not_local = function
    | Var v -> Program.is_global prog v
    | _ -> true
    in
    (* separate the expressions over locals from the expression over globals *)
    let rec t_e mk_fun = function
        | (BinEx (AND, l, r)) as e ->
            if expr_exists is_global e
            then BinEx (AND, t_e mk_fun l, t_e mk_fun r)
            else mk_fun (eval_bool_expr e)
        | (BinEx (OR, l, r)) as e ->
            if expr_exists is_global e
            then BinEx (OR, t_e mk_fun l, t_e mk_fun r)
            else mk_fun (eval_bool_expr e)
        | (UnEx (NEG, l)) as e ->
            if expr_exists is_global e
            then UnEx (NEG, t_e mk_fun l)
            else mk_fun (eval_bool_expr e)
        | _ as e -> 
            if expr_forall not_local e
            then e (* leave intact, it is an expression over globals *)
            else mk_fun (eval_bool_expr e)
    in
    let rec replace_card = function
        | UnEx (CARD, BinEx (EQ, Var v, Const i)) ->
            let is_ok valuation = (i = (Hashtbl.find valuation v)) in
            let c_ctx = ctr_ctx_tbl#get_ctx v#proc_name in
            let indices = c_ctx#all_indices_for is_ok in
            let mk_sum l i =
                let arr = BinEx (ARR_ACCESS, Var c_ctx#get_ctr, Const i) in
                if not_nop l then BinEx (PLUS, l, arr) else arr
            in
            List.fold_left mk_sum (Nop "") indices
        | UnEx (CARD, _) as e ->
            raise (Failure
                (sprintf "Don't know how to handle card(%s)" (expr_s e)))
        | BinEx (tok, lhs, rhs) ->
            BinEx (tok, replace_card lhs, replace_card rhs)
        | UnEx (tok, lhs) ->
            UnEx (tok, replace_card lhs)
        | _ as e -> e
    in
    let find_proc_name e =
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
        | _ -> "" in
        let name = fnd e in
        if name = ""
        then raise (Abstraction_error ("Atomic: No process name in " ^ (expr_s e)))
        else name
    in
    let join_two op l r =
        match (l, r) with
        | PropGlob lg, PropGlob rg ->
            PropGlob (BinEx (op, lg, rg))
        | _ -> raise (Abstraction_error "Illegal tr_atomic")
    in
    let rec tr_atomic = function
        | PropAll e ->
            let c_ctx = ctr_ctx_tbl#get_ctx (find_proc_name e) in
            PropGlob (t_e (mk_all c_ctx) e)
        | PropSome e ->
            let c_ctx = ctr_ctx_tbl#get_ctx (find_proc_name e) in
            PropGlob (t_e (mk_some c_ctx) e)
        | PropGlob e ->
            let has_card = function
                | UnEx (CARD, _) -> true
                | _ -> false
            in
            if expr_exists has_card e
            then PropGlob (replace_card e)
            else PropGlob e
        | PropAnd (l, r) ->
            join_two AND (tr_atomic l) (tr_atomic r)
        | PropOr (l, r) ->
            join_two OR (tr_atomic l) (tr_atomic r)
    in
    tr_atomic atomic_expr


(* TODO: find out the values at the end of the init_stmts,
   not the accumulated values
   *)
let find_init_local_vals ctr_ctx decls init_stmts =
    let init_cfg = Cfg.mk_cfg (mir_to_lir (decls @ init_stmts)) in
    let int_roles =
        visit_cfg (visit_basic_block transfer_roles)
            (join lub_int_role) (print_int_roles "local roles") init_cfg in
    let init_sum =
        join_all_locs (join lub_int_role) (mk_bottom_val ()) int_roles in
    let mk_prod left right =
        if left = []
        then List.map (fun x -> [x]) right
        else List.concat
            (List.map (fun r -> List.map (fun l -> l @ [r]) left) right) in
    List.fold_left
        (fun lst v ->
            let r =
                try Hashtbl.find init_sum v
                with Not_found ->
                    let m = (sprintf
                        "Variable %s not found in the init section"
                        v#get_name) in
                    raise (Abstraction_error m)
            in
            match r with
            | IntervalInt (a, b) ->
                let pairs =
                    List.map (fun i -> (v, i)) (range a (b + 1)) in
                mk_prod lst pairs
            | _ ->
                let m = sprintf
                    "Unbounded after abstraction: %s" v#get_name in
                raise (Abstraction_error m)
        ) [] ctr_ctx#var_vec


(* remove assignments to local variables from the initialization section *)
let omit_local_assignments prog init_stmts =
    let rec tr = function
        | MExpr (id, BinEx(ASGN, Var v, rhs)) as s ->
            if Program.is_global prog v
            then s
            else MExpr (id, Nop ("/* " ^ (mir_stmt_s s) ^ " */"))
        | MAtomic (id, seq) ->
                MAtomic (id, List.map tr seq)
        | MD_step (id, seq) ->
                MD_step (id, List.map tr seq)
        | MIf (id, opts) ->
                MIf (id, List.map tr_opt opts)
        | _ as s -> s
    and tr_opt = function
        | MOptGuarded seq -> MOptGuarded (List.map tr seq)
        | MOptElse seq -> MOptElse (List.map tr seq)
    in
    List.map tr init_stmts


(* abstraction of functions different in VASS and our counter abstraction *)
class virtual ctr_funcs =
    object
        method virtual introduced_vars:
            var list

        method virtual mk_pre_loop:
            ctr_abs_ctx -> token expr -> token mir_stmt list
        method virtual mk_pre_asserts:
            ctr_abs_ctx -> token expr -> token expr -> token expr -> token mir_stmt list
        method virtual mk_post_asserts:
            ctr_abs_ctx -> token expr -> token expr -> token expr -> token mir_stmt list
        method virtual mk_init:
            ctr_abs_ctx -> token expr -> token mir_stmt list -> token mir_stmt list
            -> token mir_stmt list

        method virtual mk_counter_update:
            ctr_abs_ctx -> token expr -> token expr -> token mir_stmt list

        method deref_ctr (c_ctx: ctr_abs_ctx) (e: token expr): token expr =
            BinEx (ARR_ACCESS, Var c_ctx#get_ctr, e)

        method virtual keep_assume:
            token expr -> bool

        method virtual embed_inv: bool
        method virtual set_embed_inv: bool -> unit
    end


class abs_ctr_funcs dom prog solver =
    object(self)
        inherit ctr_funcs

        method introduced_vars = []

        method mk_pre_loop c_ctx active_expr =
            []

        method mk_pre_asserts c_ctx active_expr prev_idx next_idx =
            []

        method mk_post_asserts c_ctx active_expr prev_idx next_idx =
            let n = c_ctx#get_ctr_dim in
            let m = List.length (Program.get_shared prog) in
            let str = sprintf "%s:GS{%%d->%%d:{%s},%s}\\n"
                c_ctx#abbrev_name
                (String.concat "," (Accums.n_copies n "%d"))
                (String.concat "," (Accums.n_copies m "%d")) in
            let mk_deref i = self#deref_ctr c_ctx (Const i) in
            let es = (List.map mk_deref (range 0 n))
                @ (List.map (fun v -> Var v) (Program.get_shared prog)) in
            
            [ MPrint (-1, str, prev_idx :: next_idx :: es)]

        method mk_init c_ctx active_expr decls init_stmts =
            let init_locals = find_init_local_vals c_ctx decls init_stmts in
            let size_dist_list =
                dom#scatter_abs_vals
                    solver active_expr (List.length init_locals) in
            let mk_option local_vals abs_size =
                let valuation = Hashtbl.create 10 in
                let add_var (var, i) = Hashtbl.add valuation var i in
                List.iter add_var local_vals;
                let idx = c_ctx#pack_to_const valuation in
                let lhs = BinEx (ARR_ACCESS, Var c_ctx#get_ctr, Const idx) in
                MExpr (-1, BinEx (ASGN, lhs, Const abs_size))
            in
            let option_list =
                List.map
                    (fun d -> List.map2 mk_option init_locals d
                    ) size_dist_list
            in
            (omit_local_assignments prog init_stmts)
            @ 
            (mk_nondet_choice option_list)
                @ self#mk_post_asserts c_ctx active_expr (Const (-1)) (Const 0)

        method mk_counter_update c_ctx prev_idx next_idx =
            let mk_one tok idx_ex = 
                let ktr_i = self#deref_ctr c_ctx idx_ex in
                let is_deref = function
                    | BinEx (ARR_ACCESS, _, _) -> true
                    | _ -> false
                in
                let expr_abs_vals =
                    mk_expr_abstraction solver dom is_deref
                        (BinEx (tok, ktr_i, Const 1)) in
                mk_assign_unfolding ktr_i expr_abs_vals
            in
            let guard = MExpr(-1, BinEx (NE, prev_idx, next_idx)) in
            let seq = [guard; mk_one MINUS prev_idx; mk_one PLUS next_idx] in
            let comment = "processes stay at the same local state" in
            [MIf (-1, [MOptGuarded seq; MOptElse [MExpr(-1, Nop comment)]])]

        method keep_assume e = false
        
        method embed_inv = false
        method set_embed_inv _ = ()
    end


class vass_funcs dom prog solver =
    object(self)
        inherit ctr_funcs

        (* a free variable delta describing how many processes made a step *)
        val mutable delta = new var "vass_dta"

        val mutable m_embed_inv = true

        method introduced_vars = [delta]

        method mk_pre_loop c_ctx active_expr =
            [MHavoc (-1, delta);
             MAssume (-1, BinEx (GT, Var delta, Const 0));]

        method mk_pre_asserts c_ctx active_expr prev_idx next_idx =
            let acc i = BinEx (ARR_ACCESS, Var c_ctx#get_ctr, Const i) in
            let add s i = if s <> Const 0 then BinEx (PLUS, acc i, s) else acc i
            in
            (* counter are non-negative, non-obvious for an SMT solver! *)
            let all_indices = (range 0 c_ctx#get_ctr_dim) in
            let mk_non_neg i = MAssume (-1, BinEx (GE, acc i, Const 0)) in
            (* the sum of counters is indeed the number of processes! *)
            (* though it is preserved in VASS, it is lost in the counter abs. *)
            let sum =
                List.fold_left add (Const 0) (range 0 c_ctx#get_ctr_dim) in
            MAssume (-1, BinEx (EQ, active_expr, sum));
            :: (List.map mk_non_neg all_indices)

        method mk_post_asserts c_ctx active_expr prev_idx next_idx =
            self#mk_pre_asserts c_ctx active_expr prev_idx next_idx

        method mk_init c_ctx active_expr decls init_stmts =
            let init_locals = find_init_local_vals c_ctx decls init_stmts in
            let has_val valuation =
                let same_var (x, (i: int)) = (i = (Hashtbl.find valuation x)) in
                let same_asgn lst = List.for_all same_var lst in
                try List.exists same_asgn init_locals
                with Not_found -> false
            in
            let indices = c_ctx#all_indices_for has_val in
            let sum_fun e i =
                let ctr_ex = BinEx (ARR_ACCESS, Var c_ctx#get_ctr, Const i)
                in
                if is_nop e then ctr_ex else BinEx (PLUS, e, ctr_ex)
            in
            let sum_ex = List.fold_left sum_fun (Nop "") indices in
            let sum_eq_n = MAssume (-1, BinEx (EQ, active_expr, sum_ex)) in
            let other_indices =
                List.filter (fun i -> not (List.mem i indices))
                    (range 0 c_ctx#get_ctr_dim) in
            let mk_oth i = MAssume (-1, BinEx (EQ, Const 0, sum_fun (Nop "") i))
            in
            let other0 = List.map mk_oth other_indices in
            (omit_local_assignments prog init_stmts)
            @ sum_eq_n :: other0
                @ (self#mk_post_asserts c_ctx active_expr (Const 0) (Const 0))

        method mk_counter_update c_ctx prev_idx next_idx =
            (* XXX: use a havoc-like operator here *)
            (* it is very important that we add delta instead of 1 here,
               as it describes a summary of several processes doing the same
               step *)
            let mk_one tok idx_ex =
                let ktr_i = self#deref_ctr c_ctx idx_ex in
                MExpr (-1, BinEx (ASGN, ktr_i, BinEx (tok, ktr_i, Var delta)))
            in

            let guard = MExpr(-1, BinEx (NE, prev_idx, next_idx)) in
            let nonneg = MAssume (-1,
                BinEx (GE, self#deref_ctr c_ctx prev_idx, Var delta)) in
            let seq = [guard; nonneg;
                mk_one MINUS prev_idx; mk_one PLUS next_idx] in
            let comment = "processes stay at the same local state" in
            [MIf (-1, [MOptGuarded seq; MOptElse [MExpr(-1, Nop comment)]])]

        method keep_assume e = true
        
        method embed_inv = m_embed_inv
        method set_embed_inv v = m_embed_inv <- v
    end


let fuse_ltl_form ctr_ctx_tbl fairness name ltl_expr =
    let embed_fairness fair_expr no_inf_forms =
        let spur = UnEx(ALWAYS, UnEx(NEG, Var ctr_ctx_tbl#get_spur)) in
        let spur_and_fair =
            if is_nop fair_expr then [spur] else [spur; fair_expr] in
        let precond = list_to_binex AND (spur_and_fair @ no_inf_forms) in
        BinEx(IMPLIES, precond, ltl_expr)
    in
    let form = if (name <> "fairness") && (not_nop fairness)
    then begin
        (* add formulas saying that unfair predicates can't occur forever *)
        let recur_preds_cnt = (1 + (find_max_pred pred_recur)) in
        let mk_fair i =
            let r_var = Var (new var (sprintf "bymc_%s%d" pred_recur i)) in
            UnEx(ALWAYS, UnEx(EVENTUALLY, UnEx(NEG, r_var)))
        in
        let no_inf_forms = List.map mk_fair (range 0 recur_preds_cnt) in
        embed_fairness fairness no_inf_forms
    end else ltl_expr in
    form

(* Transform the program using counter abstraction over the piaDomain.
   Updates proc_struct_cache#regions.
 *)
let do_counter_abstraction funcs solver caches prog =
    let t_ctx = caches#get_analysis#get_pia_data_ctx in
    let roles = caches#get_analysis#get_var_roles in
    let ctr_ctx_tbl = caches#get_analysis#get_pia_ctr_ctx_tbl in
    let extract_atomic_prop atomics name =
        try
            match (Program.StringMap.find name atomics) with
            | PropGlob e -> e
            | _ -> raise (Abstraction_error ("Cannot extract " ^ name))
        with Not_found ->
            raise (Abstraction_error ("No atomic expression: " ^ name))
    in
    let replace_assume atomics = function
        | MAssume (id, Var v) as s ->
            if funcs#keep_assume (Var v)
            then 
                if v#proc_name = "spec"
                then MAssume (id, extract_atomic_prop atomics v#get_name)
                else s
            else MSkip id
        | _ as s -> s
    in
    let counter_guard c_ctx =
        let make_opt idx =
            let guard =
                (BinEx (NE,
                    BinEx (ARR_ACCESS, Var c_ctx#get_ctr, Const idx),
                    Const 0))
            in
            MExpr (-1, guard) :: (* and then assignments *)
                (Hashtbl.fold
                    (fun var value lst -> 
                        MExpr (-1, BinEx (ASGN, Var var, Const value)) :: lst)
                    (c_ctx#unpack_from_const idx) [])
        in
        let indices = range 0 c_ctx#get_ctr_dim in
        mk_nondet_choice (List.map make_opt indices)
    in
    let replace_update c_ctx active_expr update atomics stmts =
        (* all local variables should be reset to 0 *)
        let new_update =
            let replace_expr = function
                | MExpr (_1, BinEx (ASGN, Var var, rhs)) as s ->
                    begin
                        match roles#get_role var with
                        | LocalUnbounded
                        | BoundedInt (_, _) ->
                            MExpr (-1, BinEx (ASGN, Var var, Const 0))
                        | _ -> s
                    end
                | _ as s -> s
            in
            List.map (fun e -> replace_assume atomics (replace_expr e)) update
        in
        let prev_next_pairs = find_copy_pairs (mir_to_lir update) in
        let prev_idx_ex = c_ctx#pack_index_expr in
        let next_idx_ex =
            map_vars
                (fun v ->
                    try Var (Hashtbl.find prev_next_pairs v)
                    with Not_found -> Var v
                ) prev_idx_ex in
        let pre_asserts =
            funcs#mk_pre_asserts c_ctx active_expr prev_idx_ex next_idx_ex in
        let post_asserts =
            funcs#mk_post_asserts c_ctx active_expr prev_idx_ex next_idx_ex in

        pre_asserts
        @ (funcs#mk_counter_update c_ctx prev_idx_ex next_idx_ex)
        @ [MUnsafe (-1, "#include \"cegar_post.inc\"")]
        @ post_asserts
        @ new_update
    in
    let replace_comp atomics stmts =
        let rec hack_nsnt = function
            (* XXX: this is a hack saying if we have nsnt + 1,
                then it must be nsnt + delta *)
            | MExpr (id, BinEx (ASGN, Var x, BinEx (PLUS, Var y, Const 1))) as s ->
                if t_ctx#must_keep_concrete (Var x) && x#get_name = y#get_name
                then MExpr (id,
                        BinEx (ASGN, Var x,
                            BinEx (PLUS, Var x, Var (new var "vass_dta"))))
                else s
            | MIf (id, opts) ->
                let on_opt = function
                    | MOptGuarded seq -> MOptGuarded (List.map hack_nsnt seq)
                    | MOptElse seq -> MOptElse (List.map hack_nsnt seq)
                in
                MIf (id, (List.map on_opt opts))
            | _ as s -> s
        in
        List.map hack_nsnt (List.map (replace_assume atomics) stmts)
    in
    let mk_assume e = MAssume (-1, e) in
    let abstract_proc atomics p =
        let c_ctx = ctr_ctx_tbl#get_ctx p#get_name in
        let invs = if funcs#embed_inv
            then List.map mk_assume (find_invariants atomics)
            else [] in
        let body = remove_bad_statements p#get_stmts in
        (* TODO: figure out why the order of the following calls affects
           the number of refinement steps! *)
        let reg_tab = extract_skel body in
        let main_lab = mk_uniq_label () in
        let new_init =
            funcs#mk_init c_ctx p#get_active_expr
            (reg_tab#get "decl") (reg_tab#get "init") in
        let new_update =
            replace_update c_ctx p#get_active_expr
            (reg_tab#get "update") atomics body in
        let new_comp = replace_comp atomics (reg_tab#get "comp") in
        let new_comp_upd = MAtomic (-1, new_comp @ new_update @ invs) in
        let new_loop_body =
            [MUnsafe (-1, "#include \"cegar_pre.inc\"")]
            @ (funcs#mk_pre_loop c_ctx p#get_active_expr)
            @ invs
            @ counter_guard c_ctx
            @ [MIf (-1, [MOptGuarded ([new_comp_upd])]);
               MGoto (-1, main_lab)] in
        let new_prefix =
            (MLabel (-1, main_lab)) :: (reg_tab#get "loop_prefix") in
        let new_body = 
            (reg_tab#get "decl")
            @ new_init
            @ new_prefix
            @ new_loop_body
        in
        let new_reg_tbl = new region_tbl in
        new_reg_tbl#add "decl" (reg_tab#get "decl");
        new_reg_tbl#add "init" new_init;
        new_reg_tbl#add "loop_prefix" new_prefix;
        new_reg_tbl#add "comp" new_comp;
        new_reg_tbl#add "update" new_update;
        new_reg_tbl#add "loop_body" new_loop_body;
        caches#get_struc#set_regions p#get_name new_reg_tbl;
        let new_proc = proc_replace_body p new_body in
        new_proc#set_active_expr (Const 1);
        new_proc#set_provided (BinEx (EQ, Var c_ctx#get_spur, Const 0));
        new_proc
    in
    let abstract_atomic ae =
        (trans_prop_decl solver ctr_ctx_tbl prog ae)
    in
    let fairness =
        if Program.StringMap.mem "fairness" (Program.get_ltl_forms prog)
        then Program.StringMap.find "fairness" (Program.get_ltl_forms prog)
        else (Nop "") in
    let map_ltl_form name ltl_expr =
        fuse_ltl_form ctr_ctx_tbl fairness name ltl_expr
    in
    let new_atomics =
        Program.StringMap.map abstract_atomic (Program.get_atomics prog) in
    let new_procs =
        List.map (abstract_proc new_atomics) (Program.get_procs prog) in
    let new_unsafes = ["#include \"cegar_decl.inc\""] in
    let new_decls =
        ctr_ctx_tbl#get_spur
            :: ctr_ctx_tbl#all_counters @ funcs#introduced_vars in
    let new_ltl_forms =
        Program.StringMap.mapi map_ltl_form (Program.get_ltl_forms prog) in
    let new_prog =
        (Program.set_shared (Program.get_shared prog)
        (Program.set_instrumental new_decls
        (Program.set_atomics new_atomics
        (Program.set_unsafes new_unsafes
        (Program.set_ltl_forms new_ltl_forms
        (Program.set_procs new_procs (Program.empty))))))) in
    new_prog

