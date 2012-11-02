(*
  The place where we do counter abstraction w.r.t. interval domain.
  This code was written in an ad-hoc way and requires refactoring.

  Igor Konnov 2012
 *)

open Printf;;

open Accums;;
open Spin;;
open SpinIr;;
open SpinIrImp;;
open Smt;;
open Cfg;;
open Analysis;;
open Ssa;;
open SkelStruc;;
open CfgSmt;;
open Debug;;

open AbsBasics;;
open AbsInterval;;
open Refinement;;
open Ltl;;

(* Counter abstraction context. Each process prototype has its own counter
   abstraction context as the abstraction depends on the local state space.
 *)
class ctr_abs_ctx dom t_ctx proctype_name short_name =
    object(self)
        val mutable control_vars: var list = []
        val mutable control_size = 0
        val mutable data_vars = []
        val mutable var_sizes: (var, int) Hashtbl.t = Hashtbl.create 1
        val ctr_var = new var ("bymc_k" ^ short_name)
        val spur_var = new var "bymc_spur"
        
        initializer
            (* XXX: debug *)
            List.iter
                (fun v -> printf "@%s___*%s*_*%s*\n" proctype_name v#proc_name v#qual_name)
                (hashtbl_filter_keys is_bounded t_ctx#get_var_roles);
            let is_proc_var v = (v#proc_name = proctype_name) in
            let cvs = List.filter is_proc_var
                (hashtbl_filter_keys is_bounded t_ctx#get_var_roles) in
            if cvs == []
            then begin
                let m = "No status variable (like pc) in "
                    ^ proctype_name ^ " found." in
                raise (Abstraction_error m)
            end;
            control_vars <- cvs;
            let var_dom_size v =
                match t_ctx#get_role v with
                | BoundedInt (a, b) ->
                    if is_proc_var v then (b - a) + 1 else 1
                | _ -> 1
            in
            control_size <- List.fold_left ( * ) 1 (List.map var_dom_size control_vars);
            List.iter (fun v -> Hashtbl.add var_sizes v (var_dom_size v)) control_vars;
            let dvs = List.filter is_proc_var
                (hashtbl_filter_keys is_local_unbounded t_ctx#get_var_roles) in
            data_vars <- dvs;
            List.iter (fun v -> Hashtbl.add var_sizes v dom#length) data_vars;
            ctr_var#set_isarray true;
            ctr_var#set_num_elems
                ((ipow dom#length (List.length data_vars))  * control_size);
            spur_var#set_type SpinTypes.TBIT
           
        method get_control_vars = control_vars
        method get_control_size = control_size
        method get_locals = data_vars
        method get_ctr = ctr_var
        method get_ctr_dim = ctr_var#get_num_elems
        method get_spur = spur_var

        method var_vec = (self#get_locals @ self#get_control_vars)

        method unpack_from_const i =
            let vsz v = Hashtbl.find var_sizes v in
            let valuation = Hashtbl.create (List.length self#var_vec) in
            let unpack_one big_num var =
                Hashtbl.add valuation var (big_num mod (vsz var));
                big_num / (vsz var) in
            let _ = List.fold_left unpack_one i self#var_vec in
            valuation

        method pack_to_const valuation =
            let get_val var =
                try Hashtbl.find valuation var
                with Not_found ->
                    raise (Failure
                        (sprintf "Valuation of %s not found" var#get_name))
            in
            let pack_one sum var =
                sum * (Hashtbl.find var_sizes var) + (get_val var) in
            List.fold_left pack_one 0 (List.rev self#var_vec)

        method pack_index_expr =
            let pack_one subex var =
                if is_nop subex
                then Var var
                else let shifted =
                        BinEx (MULT, subex, Const (Hashtbl.find var_sizes var)) in
                    BinEx (PLUS, shifted, Var var)
            in
            List.fold_left pack_one (Nop "") (List.rev self#var_vec)

        method all_indices_for check_val_fun =
            let has_v i = (check_val_fun (self#unpack_from_const i)) in
            List.filter has_v (range 0 self#get_ctr_dim)
    end
;;


(* Collection of counter abstraction contexts: one for a process prototype. *)
class ctr_abs_ctx_tbl dom t_ctx units =
    object(self)
        val mutable tbl: (string, ctr_abs_ctx) Hashtbl.t
            = Hashtbl.create (List.length units)
        val spur_var = new var "bymc_spur"
        
        initializer
            let mk = function
                | Proc p ->
                    let pname = p#get_name in
                    let s = str_shorten tbl pname in
                    Hashtbl.add tbl pname (new ctr_abs_ctx dom t_ctx pname s)
                | _ -> ()
            in
            List.iter mk units

        method get_ctx name =
            try Hashtbl.find tbl name
            with Not_found -> raise (Failure ("No context for " ^ name))

        method all_counters =
            List.map (fun c -> c#get_ctr) (hashtbl_vals tbl)

        method get_spur = spur_var
    end
;;


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
;;

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
;;

let trans_prop_decl t_ctx ctr_ctx_tbl dom solver decl_expr =
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
    let rec t_e mk_fun = function
        | BinEx (EQ, Var v, Const c) as e ->
            if not (t_ctx#is_global v)
            then mk_fun (fun m -> c = (Hashtbl.find m v))
            else e
        | BinEx (EQ, Const c, Var v) ->
            t_e mk_fun (BinEx (EQ, Var v, Const c))
        | BinEx (NE, Var v, Const c) as e ->
            if not (t_ctx#is_global v)
            then mk_fun (fun m -> c <> (Hashtbl.find m v))
            else e
        | BinEx (NE, Const c, Var v) ->
            t_e mk_fun (BinEx (NE, Var v, Const c))
        | BinEx (AND, l, r) ->
            BinEx (AND, t_e mk_fun l, t_e mk_fun r)
        | BinEx (OR, l, r) ->
            BinEx (OR, t_e mk_fun l, t_e mk_fun r)
        | UnEx (NEG, s) ->
            UnEx (NEG, t_e mk_fun s)
        | _ as e ->
            let not_local = function
            | Var v -> t_ctx#is_global v
            | _ -> true
            in
            if not (expr_forall not_local e)
            then raise (Abstraction_error
                (sprintf "Don't know how to do counter abstraction for %s"
                    (expr_s e)))
            else e (* do not touch *)
    in
    let rec repl_ctr = function
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
            BinEx (tok, repl_ctr lhs, repl_ctr rhs)
        | UnEx (tok, lhs) ->
            UnEx (tok, repl_ctr lhs)
        | _ as e -> e
    in
    let rec find_proc_name = function
        | Var v -> v#proc_name
        | BinEx (_, l, r) ->
                let ln, rn = find_proc_name l, find_proc_name r in
                if ln <> rn && ln <> "" && rn <> ""
                then let m = (sprintf "2 procs in one property: %s <> %s" ln rn)
                in raise (Failure m)
                else if ln <> "" then ln else rn
        | UnEx (_, l) -> find_proc_name l
        | _ -> ""
    in
    match decl_expr with
        | MDeclProp (id, v, PropAll e) ->
            let c_ctx = ctr_ctx_tbl#get_ctx (find_proc_name e) in
            t_e (mk_all c_ctx) e
        | MDeclProp (id, v, PropSome e) ->
            let c_ctx = ctr_ctx_tbl#get_ctx (find_proc_name e) in
            t_e (mk_some c_ctx) e
        | MDeclProp (id, v, PropGlob e) ->
            let has_card = function
                | UnEx (CARD, _) -> true
                | _ -> false
            in
            if expr_exists has_card e then repl_ctr e else e
        | _ as s ->
            raise (Abstraction_error ("Don't know how to handle " ^ (mir_stmt_s s)))
;;

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
;;

(* remove assignments to local variables from the initialization section *)
let omit_local_assignments ctx init_stmts =
    let rec tr = function
        | MExpr (id, BinEx(ASGN, Var v, rhs)) as s ->
            if ctx#is_global v
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
;;


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
    end;;


class abs_ctr_funcs dom t_ctx solver =
    object(self)
        inherit ctr_funcs

        method introduced_vars = []

        method mk_pre_loop c_ctx active_expr =
            []

        method mk_pre_asserts c_ctx active_expr prev_idx next_idx =
            []

        method mk_post_asserts c_ctx active_expr prev_idx next_idx =
            let n = c_ctx#get_ctr_dim in
            let m = List.length t_ctx#get_shared in
            let str = sprintf "GS{%%d->%%d:%s}\\n"
                (String.concat "," (Accums.n_copies (n + m) "%d")) in
            let mk_deref i = self#deref_ctr c_ctx (Const i) in
            let es = (List.map mk_deref (range 0 n))
                @ (List.map (fun v -> Var v) t_ctx#get_shared) in
            
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
            (omit_local_assignments t_ctx init_stmts)
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
    end;;


class vass_funcs dom t_ctx solver =
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
            (omit_local_assignments t_ctx init_stmts)
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
    end;;


let fuse_ltl_form ctr_ctx_tbl ltl_forms name ltl_expr =
    let embed_fairness fair_expr no_inf_forms =
        let spur = UnEx(ALWAYS, UnEx(NEG, Var ctr_ctx_tbl#get_spur)) in
        let spur_and_fair =
            if is_nop fair_expr then [spur] else [spur; fair_expr] in
        let precond = list_to_binex AND (spur_and_fair @ no_inf_forms) in
        BinEx(IMPLIES, precond, ltl_expr)
    in
    Hashtbl.add ltl_forms name ltl_expr;
    if (name <> "fairness") && (Hashtbl.mem ltl_forms "fairness")
    then begin
        (* add formulas saying that unfair predicates can't occur forever *)
        let recur_preds_cnt = (1 + (find_max_pred pred_recur)) in
        let mk_fair i =
            let r_var = Var (new var (sprintf "bymc_%s%d" pred_recur i)) in
            UnEx(ALWAYS, UnEx(EVENTUALLY, UnEx(NEG, r_var)))
        in
        let no_inf_forms = List.map mk_fair (range 0 recur_preds_cnt) in
        (* Spin 6.2 does not support inline formulas longer that 1024 chars.
           Put the formula into the file. *)
        let fairness =
            try (Hashtbl.find ltl_forms "fairness")
            with Not_found ->
                raise (Abstraction_error "No \"fairness\" ltl formula found")
        in
        let embedded = embed_fairness fairness no_inf_forms in
        let out = open_out (sprintf "%s.ltl" name) in
        fprintf out "%s\n" (expr_s embedded);
        close_out out
    end;
    None
;;


let do_counter_abstraction t_ctx dom solver ctr_ctx_tbl funcs units =
    let atomic_props = Hashtbl.create 10 in
    let ltl_forms = Hashtbl.create 10 in
    let extract_atomic_prop name =
        try
            match (Hashtbl.find atomic_props name) with
            | PropGlob e -> e
            | _ -> raise (Abstraction_error ("Cannot extract " ^ name))
        with Not_found ->
            raise (Abstraction_error ("No atomic expression: " ^ name))
    in
    let replace_assume = function
        | MAssume (id, Var v) as s ->
            if funcs#keep_assume (Var v)
            then 
                if v#proc_name = "spec"
                then MAssume (id, extract_atomic_prop v#get_name)
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
    let replace_update c_ctx active_expr update stmts =
        (* all local variables should be reset to 0 *)
        let new_update =
            let replace_expr = function
                | MExpr (_1, BinEx (ASGN, Var var, rhs)) as s ->
                    begin
                        match t_ctx#get_role var with
                        | LocalUnbounded
                        | BoundedInt (_, _) ->
                            MExpr (-1, BinEx (ASGN, Var var, Const 0))
                        | _ -> s
                    end
                | _ as s -> s
            in
            List.map (fun e -> replace_assume (replace_expr e)) update
        in
        let prev_next_pairs = find_copy_pairs (mir_to_lir update) in
        (* XXX: it might break with several process prototypes *)
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
    let replace_comp stmts =
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
        List.map hack_nsnt (List.map replace_assume stmts)
    in
    let mk_assume e = MAssume (-1, e) in
    let xducers = Hashtbl.create 1 in (* transition relations in SMT *)
        let abstract_proc c_ctx p =
        let invs = if funcs#embed_inv
            then List.map mk_assume (find_invariants atomic_props)
            else [] in
        let body = remove_bad_statements p#get_stmts in
        let skel = extract_skel body in
        let main_lab = mk_uniq_label () in
        let new_init = funcs#mk_init c_ctx p#get_active_expr skel.decl skel.init in
        let new_update = replace_update c_ctx p#get_active_expr skel.update body in
        let new_comp = replace_comp skel.comp in
        let new_comp_upd = MAtomic (-1, new_comp @ new_update @ invs) in
        let new_loop_body =
            [MUnsafe (-1, "#include \"cegar_pre.inc\"")]
            @ (funcs#mk_pre_loop c_ctx p#get_active_expr)
            @ invs
            @ counter_guard c_ctx
            @ [MIf (-1,
                [MOptGuarded ([new_comp_upd])]);
               MGoto (-1, main_lab)] in
        let new_body = 
            skel.decl
            @ new_init
            @ [MLabel (-1, main_lab)]
            @ skel.loop_prefix
            @ new_loop_body
        in
        let new_proc = proc_replace_body p new_body in
        new_proc#set_active_expr (Const 1);
        (* SMT xducer: exactly at this moment we have all information to
           generate a xducer of a process *)
        let lirs = (mir_to_lir (new_loop_body @ [MLabel (-1, main_lab)])) in
        let all_vars =
            (c_ctx#get_ctr :: t_ctx#get_shared) @ funcs#introduced_vars in
        let cfg = mk_ssa true all_vars t_ctx#get_non_shared (mk_cfg lirs) in
        if may_log DEBUG
        then print_detailed_cfg ("Loop of " ^ p#get_name ^ " in SSA: " ) cfg;
        let transd = cfg_to_constraints cfg in
        Hashtbl.add xducers p#get_name (new proc_xducer p transd);
        Cfg.write_dot (sprintf "ssa_%s.dot" p#get_name) cfg;
        (* end of xducer *)
        new_proc
    in

    let abs_unit = function
    | Proc p ->
        let c_ctx = ctr_ctx_tbl#get_ctx p#get_name in
        let np = abstract_proc c_ctx p in
        np#set_provided (BinEx (EQ, Var c_ctx#get_spur, Const 0));
        Proc np

    | Stmt (MDeclProp (id, v, _) as d) ->
        begin
            let trd = (trans_prop_decl t_ctx ctr_ctx_tbl dom solver d) in
            Hashtbl.add atomic_props v#get_name (PropGlob trd);
            Stmt (MDeclProp (id, v, PropGlob trd))
        end

    | Ltl(name, ltl_expr) ->
        fuse_ltl_form ctr_ctx_tbl ltl_forms name ltl_expr

    | _ as u -> u
    in
    let new_units = List.map abs_unit units in
    let keep_unit = function
        | Stmt (MDecl (_, v, _)) -> not v#is_symbolic
        | Stmt (MAssume (_, _)) -> false
        | Stmt (MSkip _) -> false
        | _ -> true
    in
    let ctr_decls =
        List.map (fun v -> (Stmt (MDecl (-1, v, Nop ""))))
            ctr_ctx_tbl#all_counters in
    let out_units =
        Stmt (MUnsafe (-1, "#include \"cegar_decl.inc\""))
        :: (Stmt (MDecl (-1, ctr_ctx_tbl#get_spur, Const 0)))
        :: ctr_decls 
        @  (List.filter keep_unit new_units) in
    (out_units, xducers, atomic_props, ltl_forms)
;;

