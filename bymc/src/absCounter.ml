(*
  The place where we do counter abstraction w.r.t. interval domain.
  This code was written in an ad-hoc way and requires refactoring.

  NOTE: many decisions in this code were dictated by the need to check
  the abstraction in Spin. Some operations can be done in a much more
  efficient way symbolically.

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
open SpinIrEval
open CfgSmt
open Debug

open AbsBasics
open VarRole
open AbsInterval
open Program
open PiaCtrRefinement
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
    | seqs -> [MIf (fresh_id (), List.map (fun seq -> MOptGuarded seq) seqs)]


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


(* try to evaluate a boolean expression locally and return the result *)
let is_local_sat exp valuation =
    let val_fun = function
    | Var v ->
    begin
        try Hashtbl.find valuation v
        with Not_found ->
            let m = sprintf
                "Variable %s is not local; impossible to locally evaluate %s"
                v#qual_name (expr_s exp)
            in
            raise (Failure m)
    end

    | _ -> raise (Failure "Variable expected")
    in
    match eval_expr val_fun exp with
    | Bool b -> b
    | Int _ -> raise (Failure
        ("Expected boolean, found int: %s" ^ (expr_s exp)))


(* Translate an atomic proposition. The interesting cases are
 all(...), some(...), and card(...) that are translated to
 the expressions over counters.
 *)
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
                (sprintf
                  "Don't know how to do counter abstraction of %s in a property"
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
        | UnEx (CARD, rhs) ->
            let proc_name = Ltl.find_proc_name ~err_not_found:true rhs in
            let c_ctx = ctr_ctx_tbl#get_ctx proc_name in
            let indices = c_ctx#all_indices_for (is_local_sat rhs) in
            let mk_sum l i =
                let arr = BinEx (ARR_ACCESS, Var c_ctx#get_ctr, Const i)
                in
                if not_nop l then BinEx (PLUS, l, arr) else arr
            in
            List.fold_left mk_sum (Nop "") indices

        | BinEx (tok, lhs, rhs) ->
            BinEx (tok, replace_card lhs, replace_card rhs)

        | UnEx (tok, lhs) ->
            UnEx (tok, replace_card lhs)

        | _ as e -> e
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


(* a hack around trans_prop_decl *)
let trans_quantifiers solver ctr_ctx_tbl prog stmt =
    let omit_glob = function
    | PropGlob e -> e
    | _ -> raise (Abstraction_error "Expected PropGlob")
    in
    let rec map = function
    | UnEx (ALL, e) ->
        omit_glob (trans_prop_decl solver ctr_ctx_tbl prog (PropAll e))
    | UnEx (SOME, e) ->
        omit_glob (trans_prop_decl solver ctr_ctx_tbl prog (PropSome e))
    | UnEx (t, e) ->
        UnEx (t, map e)
    | BinEx (t, l, r) ->
        BinEx (t, map l, map r)
    | _ as e -> e
    in           
    map_expr_in_stmt map stmt



(* remove assignments to local variables from the initialization section *)
let omit_local_assignments prog init_stmts =
    let rec tr = function
        | MExpr (id, BinEx(ASGN, Var v, rhs)) as s ->
            if Program.is_global prog v
            then s
            else MExpr (id, Nop (mir_stmt_s s))
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


(* abstraction of functions different in VASS and in the (explicit) counter abstraction *)
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

        method virtual mk_counter_guard:
            ctr_abs_ctx -> token mir_stmt list

        method virtual mk_counter_update:
            ctr_abs_ctx -> (var * var) list ->
            token expr -> token expr -> token mir_stmt list

        method deref_ctr (c_ctx: ctr_abs_ctx) (e: token expr): token expr =
            BinEx (ARR_ACCESS, Var c_ctx#get_ctr, e)

        method virtual transform_inc:
            PiaDataCtx.pia_data_ctx -> token mir_stmt -> token mir_stmt

        method virtual keep_assume:
            token expr -> bool

        method virtual embed_inv: bool
        method virtual set_embed_inv: bool -> unit

        method virtual register_new_vars: ctr_abs_ctx_tbl -> data_type_tab -> unit
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
            [ ]


        method mk_init c_ctx active_expr decls init_stmts =
            let init_locals =
                SkelStruc.comp_seq c_ctx#var_vec (decls @ init_stmts) in
            let size_dist_list =
                dom#scatter_abs_vals
                    solver active_expr (List.length init_locals) in
            let mk_option local_vals abs_size =
                let valuation = Hashtbl.create 10 in
                let add_var (var, i) = Hashtbl.add valuation var i in
                List.iter add_var local_vals;
                let idx = c_ctx#pack_to_const valuation in
                let lhs = BinEx (ARR_ACCESS, Var c_ctx#get_ctr, Const idx) in
                MExpr (fresh_id (), BinEx (ASGN, lhs, Const abs_size))
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

        method mk_counter_guard c_ctx =
            let make_opt idx =
                let guard =
                    (BinEx (NE,
                        BinEx (ARR_ACCESS, Var c_ctx#get_ctr, Const idx),
                        Const 0))
                in
                MExpr (fresh_id (), guard) :: (* and then assignments *)
                    (Hashtbl.fold
                        (fun var value lst -> 
                            MExpr (fresh_id (),
                                   BinEx (ASGN, Var var, Const value)) :: lst)
                        (c_ctx#unpack_from_const idx) [])
            in
            let indices = range 0 c_ctx#get_ctr_dim in
            mk_nondet_choice (List.map make_opt indices)


        method mk_counter_update c_ctx prev_next_list prev_idx next_idx =
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
            let mk_ne (prev, next) = BinEx (NE, Var prev, Var next) in
            let gexpr = list_to_binex OR (List.map mk_ne prev_next_list)
            in
            let guard = MExpr(fresh_id (), gexpr) in
            let seq = [guard; mk_one MINUS prev_idx; mk_one PLUS next_idx] in
            let comment = "processes stay at the same local state" in
            [MIf (fresh_id (),
                  [MOptGuarded seq;
                   MOptElse [ MExpr(fresh_id (), Nop comment)]])
            ]

        method transform_inc _ s = s

        method keep_assume e = false
        
        method embed_inv = false
        method set_embed_inv _ = ()

        method register_new_vars c_ctx_tbl type_tbl =
            type_tbl#set_type
                c_ctx_tbl#get_spur (new data_type SpinTypes.TBIT);

            let reg_ctr ctx =
                let tp = new data_type SpinTypes.TINT in
                tp#set_range 0 dom#length; (* counters are bounded *)
                tp#set_nelems ctx#get_ctr_dim;
                type_tbl#set_type ctx#get_ctr tp
            in
            List.iter reg_ctr c_ctx_tbl#all_ctxs
    end


class vass_funcs dom prog solver =
    object(self)
        inherit ctr_funcs

        (* a free variable delta describing how many processes made a step *)
        val mutable delta = new_var "vass_dta"

        val mutable m_embed_inv = true

        method introduced_vars = [delta]

        method mk_pre_loop c_ctx active_expr =
            [MHavoc (fresh_id (), delta);
             MAssume (fresh_id (), BinEx (GT, Var delta, Const 0));]

        method mk_pre_asserts c_ctx active_expr prev_idx next_idx =
            let acc i = BinEx (ARR_ACCESS, Var c_ctx#get_ctr, Const i) in
            let add s i = if s <> Const 0 then BinEx (PLUS, acc i, s) else acc i
            in
            (* counter are non-negative, non-obvious for an SMT solver! *)
            let all_indices = (range 0 c_ctx#get_ctr_dim) in
            let mk_non_neg i =
                MAssume (fresh_id (), BinEx (GE, acc i, Const 0)) in
            (* the sum of counters is indeed the number of processes! *)
            (* though it is preserved in VASS, it is lost in the counter abs. *)
            let sum =
                List.fold_left add (Const 0) (range 0 c_ctx#get_ctr_dim) in
            MAssume (fresh_id (), BinEx (EQ, active_expr, sum));
            :: (List.map mk_non_neg all_indices)

        method mk_post_asserts c_ctx active_expr prev_idx next_idx =
            self#mk_pre_asserts c_ctx active_expr prev_idx next_idx

        method mk_init c_ctx active_expr decls init_stmts =
            let init_locals =
                SkelStruc.comp_seq c_ctx#var_vec (decls @ init_stmts) in
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
            let sum_eq_n =
                MAssume (fresh_id (), BinEx (EQ, active_expr, sum_ex)) in
            let other_indices =
                List.filter (fun i -> not (List.mem i indices))
                    (range 0 c_ctx#get_ctr_dim) in
            let mk_oth i =
                MAssume (fresh_id (), BinEx (EQ, Const 0, sum_fun (Nop "") i))
            in
            let other0 = List.map mk_oth other_indices in
            (omit_local_assignments prog init_stmts)
            @ sum_eq_n :: other0
                @ (self#mk_post_asserts c_ctx active_expr (Const 0) (Const 0))

        (* on the SMT level we can always use free variables instead
           of explicit enumeration of indices *)
        method mk_counter_guard c_ctx =
            let prevs = List.map fst c_ctx#prev_next_pairs in
            let havocs = List.map (fun v -> MHavoc (fresh_id (), v)) prevs in
            let access =
                BinEx (ARR_ACCESS, Var c_ctx#get_ctr, c_ctx#pack_index_expr) in
            let ne = MExpr (fresh_id (), BinEx (NE, access, Const 0)) in
            havocs @ [ne]

        method mk_counter_update c_ctx prev_next_list prev_idx next_idx =
            (* XXX: use a havoc-like operator here *)
            (* it is very important that we add delta instead of 1 here,
               as it describes a summary of several processes doing the same
               step *)
            let mk_one tok idx_ex =
                let ktr_i = self#deref_ctr c_ctx idx_ex in
                MExpr (fresh_id (),
                       BinEx (ASGN, ktr_i, BinEx (tok, ktr_i, Var delta)))
            in
            let mk_ne (prev, next) = BinEx (NE, Var prev, Var next) in
            let gexpr = list_to_binex OR (List.map mk_ne prev_next_list)
            in
            let guard = MExpr(fresh_id (), gexpr) in
            let nonneg = MAssume (fresh_id (),
                BinEx (GE, self#deref_ctr c_ctx prev_idx, Var delta)) in
            let seq = [guard; nonneg;
                mk_one MINUS prev_idx; mk_one PLUS next_idx] in
            let comment = "processes stay at the same local state" in
            [MIf (fresh_id (),
                  [MOptGuarded seq;
                   MOptElse [MExpr(fresh_id (), Nop comment)]])]

        method transform_inc t_ctx = function
            (* XXX: this is a hack saying that if we have nsnt + 1,
                then it must be translated to nsnt + delta
                (as delta identical processes may fire at once).
                This is not needed in our current setup (FMCAD13),
                but it might be useful, when checking feasibility of a
                path (currently we are checking invividual transitions).
             *)
           | MExpr (id, BinEx (ASGN, Var x,
                    BinEx (PLUS, Var y, Const 1))) as s ->
                if t_ctx#must_keep_concrete (Var x) && x#id = y#id
                then MExpr (id,
                        BinEx (ASGN, Var x,
                            BinEx (PLUS, Var x, Var delta)))
                else s

           | _ as s -> s 

        method keep_assume e = true
        
        method embed_inv = m_embed_inv
        method set_embed_inv v = m_embed_inv <- v

        method register_new_vars c_ctx_tbl type_tbl =
            type_tbl#set_type delta (new data_type SpinTypes.TUNSIGNED);
            type_tbl#set_type
                c_ctx_tbl#get_spur (new data_type SpinTypes.TBIT);

            let reg_ctr ctx =
                let tp = new data_type SpinTypes.TUNSIGNED in
                (* NOTE: no range set, the counters are unbounded *)
                tp#set_nelems ctx#get_ctr_dim;
                type_tbl#set_type ctx#get_ctr tp
            in
            List.iter reg_ctr c_ctx_tbl#all_ctxs
    end


(* Transform the program using counter abstraction over the piaDomain.
   Updates proc_struc#regions.
 *)
let do_counter_abstraction funcs solver caches prog proc_names =
    let t_ctx = caches#analysis#get_pia_data_ctx in
    let ctr_ctx_tbl = caches#analysis#get_pia_ctr_ctx_tbl in
    let replace_update c_ctx active_expr update atomics stmts =
        (* all local variables should be reset to 0 *)
        let new_update =
            let replace_expr = function
                | MExpr (id, BinEx (ASGN, Var var, _)) as s ->
                    if var#proc_name <> ""
                    then MExpr (id, BinEx (ASGN, Var var, Const 0))
                    else s
                | _ as s -> s
            in
            List.map (fun e -> replace_expr e) update
        in
        let prev_idx_ex = c_ctx#pack_index_expr in
        let next_idx_ex =
            map_vars (fun v -> Var (c_ctx#get_next v)) prev_idx_ex in
        let pre_asserts =
            funcs#mk_pre_asserts c_ctx active_expr prev_idx_ex next_idx_ex
        in
        let post_asserts =
            funcs#mk_post_asserts c_ctx active_expr prev_idx_ex next_idx_ex
        in
        let ctr_update = funcs#mk_counter_update c_ctx
            c_ctx#prev_next_pairs prev_idx_ex next_idx_ex in
        pre_asserts
        @ [mk_comment "decrement/increment process counters"]
        @ ctr_update
        @ [MExpr (fresh_id (), Nop "assume(post_cond)")]
        @ post_asserts

        @ new_update
    in
    let replace_comp atomics stmts =
        List.map (sub_basic_stmt (trans_quantifiers solver ctr_ctx_tbl prog))
            (List.map (sub_basic_stmt (funcs#transform_inc t_ctx)) stmts)
    in
    let mk_assume e = MAssume (fresh_id (), e) in
    let abstract_proc new_struc atomics p =
        let c_ctx = ctr_ctx_tbl#get_ctx p#get_name in
        let invs = if funcs#embed_inv
            then List.map mk_assume (find_invariants atomics)
            else [] in
        let body = remove_bad_statements p#get_stmts in
        (* TODO: figure out why the order of the following calls affects
           the number of refinement steps! *)
        (* rebuild the regions, as some statements are removed *)
        let reg_tab = extract_skel body in
        let main_lab = sprintf "main%d" (mk_uniq_label ()) in
        let new_init =
            (funcs#mk_init c_ctx p#get_active_expr
                (reg_tab#get "decl" body) (reg_tab#get "init" body))
            @ [mk_comment (p#get_name ^ ": end init")]
        in
        let new_update =
            replace_update c_ctx p#get_active_expr
            (reg_tab#get "update" body) atomics body in
        let new_comp = replace_comp atomics (reg_tab#get "comp" body) in
        let new_comp_upd =
            new_comp @ new_update @ invs
                @ [mk_comment (p#get_name ^ ": end step")]
        in
        let new_loop_body =
            let in_atomic =
                [ MExpr (fresh_id (), Nop ("assume(pre_cond)"))]
                @ (funcs#mk_pre_loop c_ctx p#get_active_expr)
                @ invs
                @ [mk_comment (p#get_name ^ ": pick a process")]
                @ (funcs#mk_counter_guard c_ctx)
                @ [mk_comment (p#get_name ^ ": begin step")]
                @ new_comp_upd
            in
            [ (MAtomic (fresh_id (), in_atomic));
              (MGoto (fresh_id (), main_lab)) ]
        in
        let new_prefix =
            (MLabel (fresh_id (), main_lab)) ::
                (reg_tab#get "loop_prefix" body) in
        let new_body = 
            (reg_tab#get "decl" body)
            @ new_init
            @ new_prefix
            @ new_loop_body
        in
        (* re-construct the regions *)
        new_struc#set_regions p#get_name (extract_skel new_body);
        let new_proc = proc_replace_body p new_body in
        new_proc#set_active_expr (Const 1);
        new_proc#set_provided (BinEx (EQ, Var c_ctx#get_spur, Const 0));
        new_proc
    in
    let abstract_atomic (av, ae) =
        (av, trans_prop_decl solver ctr_ctx_tbl prog ae) in
    let new_atomics = List.map abstract_atomic (Program.get_atomics prog) in
    let new_decls = ctr_ctx_tbl#get_spur :: funcs#introduced_vars in
    let counters =
        List.map (fun v -> (v, Const 0)) ctr_ctx_tbl#all_counters in
    let new_type_tab = (Program.get_type_tab prog)#copy in
    let new_ltl_forms = (* exclude computations containing spurious states *)
        Accums.StringMap.add "fairness_ctr"
        (UnEx(ALWAYS, UnEx(NEG, Var ctr_ctx_tbl#get_spur)))
        (Program.get_ltl_forms prog) in
    funcs#register_new_vars ctr_ctx_tbl new_type_tab;
    let new_prog =
        (Program.set_params []
        (Program.set_assumes []
        (Program.set_shared_with_init
            (counters @ (Program.get_shared_with_init prog))
        (Program.set_instrumental new_decls
        (Program.set_type_tab new_type_tab
        (Program.set_atomics new_atomics
        (Program.set_ltl_forms new_ltl_forms
        Program.empty))))))) in
    let new_struc = empty_proc_struc () in
    let new_procs =
        let trp p =
            if not (List.mem p#get_name proc_names)
            then p
            else abstract_proc new_struc (Program.get_atomics_map new_prog) p in
        List.map trp (Program.get_procs prog)
    in
    let res_prog = Program.set_procs new_procs new_prog in
    caches#set_struc res_prog new_struc;
    res_prog

