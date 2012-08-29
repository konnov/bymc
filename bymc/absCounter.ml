open Printf;;

open Accums;;
open Spin;;
open Spin_ir;;
open Spin_ir_imp;;
open Smt;;
open Cfg;;
open Analysis;;
open Ssa;;
open SkelStruc;;
open CfgSmt;;
open Debug;;

open AbsInterval;;

class ctr_abs_ctx dom t_ctx =
    object(self)
        val mutable control_vars: var list = []
        val mutable control_size = 0
        val mutable data_vars = []
        val mutable var_sizes: (var, int) Hashtbl.t = Hashtbl.create 1
        val ctr_var = new var "bymc_k"
        val spur_var = new var "bymc_spur"
        
        initializer
            control_vars <- hashtbl_filter_keys is_bounded t_ctx#get_var_roles;
            if control_vars = []
            then raise (Abstraction_error "No control variables (like pc) found.");
            let var_dom_size v =
                match t_ctx#get_role v with
                | BoundedInt (a, b) -> (b - a) + 1
                | _ -> 1 in
            control_size <- List.fold_left ( * ) 1 (List.map var_dom_size control_vars);
            List.iter (fun v -> Hashtbl.add var_sizes v (var_dom_size v)) control_vars;
            data_vars <- hashtbl_filter_keys is_local_unbounded t_ctx#get_var_roles;
            List.iter (fun v -> Hashtbl.add var_sizes v dom#length) data_vars;
            ctr_var#set_isarray true;
            ctr_var#set_num_elems
                ((ipow dom#length (List.length data_vars))  * control_size);
            spur_var#set_type Spin_types.TBIT
           
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


let mk_nondet_choice seq_list =
(*
if
    :: seq_0;
    :: seq_1;
...
fi
*)
    MIf (-1, List.map (fun seq -> MOptGuarded seq) seq_list)
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

let trans_prop_decl t_ctx ctr_ctx dom solver decl_expr =
    let mk_cons tok sep indices =
        let add_cons e idx =
            let ke = BinEx (ARR_ACCESS, Var ctr_ctx#get_ctr, Const idx) in
            if is_nop e
            then BinEx (tok, ke, Const 0)
            else BinEx (sep, e, BinEx (tok, ke, Const 0)) in
        List.fold_left add_cons (Nop "") indices
    in
    let mk_all check_fun =
        mk_cons EQ AND (ctr_ctx#all_indices_for (fun m -> not (check_fun m))) in
    let mk_some check_fun =
        mk_cons NE OR (ctr_ctx#all_indices_for check_fun) in
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
            let indices = ctr_ctx#all_indices_for is_ok in
            let mk_sum l i =
                let arr = BinEx (ARR_ACCESS, Var ctr_ctx#get_ctr, Const i) in
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
    match decl_expr with
        | MDeclProp (id, v, PropAll e) ->
            MDeclProp (id, v, PropGlob (t_e mk_all e))
        | MDeclProp (id, v, PropSome e) ->
            MDeclProp (id, v, PropGlob (t_e mk_some e))
        | MDeclProp (id, v, PropGlob e) ->
            let has_card = function
                | UnEx (CARD, _) -> true
                | _ -> false
            in
            if expr_exists has_card e
            then MDeclProp (id, v, PropGlob (repl_ctr e))
            else MDeclProp (id, v, PropGlob e)
        | _ as s -> s
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

(* abstraction of functions different in VASS and our counter abstraction *)
class virtual ctr_funcs ctr_ctx =
    object
        method virtual introduced_vars:
            var list

        method virtual mk_pre_loop:
            token expr -> token mir_stmt list
        method virtual mk_pre_asserts:
            token expr -> token expr -> token expr -> token mir_stmt list
        method virtual mk_post_asserts:
            token expr -> token expr -> token expr -> token mir_stmt list
        method virtual mk_init:
            token expr -> token mir_stmt list -> token mir_stmt list
            -> token mir_stmt list
        method virtual mk_counter_update:
            token expr -> token expr -> token mir_stmt list

        method deref_ctr e =
            BinEx (ARR_ACCESS, Var ctr_ctx#get_ctr, e)

        method virtual keep_assume:
            token expr -> bool
    end;;

class abs_ctr_funcs dom t_ctx ctr_ctx solver =
    object(self)
        inherit ctr_funcs ctr_ctx 

        method introduced_vars = []

        method mk_pre_loop active_expr =
            []

        method mk_pre_asserts active_expr prev_idx next_idx =
            []

        method mk_post_asserts active_expr prev_idx next_idx =
            let n = ctr_ctx#get_ctr_dim in
            let m = List.length t_ctx#get_shared in
            let str = sprintf "GS{%%d->%%d:%s}\\n"
                (String.concat "," (Accums.n_copies (n + m) "%d")) in
            let mk_deref i = self#deref_ctr (Const i) in
            let es = (List.map mk_deref (range 0 n))
                @ (List.map (fun v -> Var v) t_ctx#get_shared) in
            let prev_ne_next =
                let sp = Var ctr_ctx#get_spur in
                let eq = BinEx (EQ, prev_idx, next_idx) in
                let e = BinEx (ASGN, sp, BinEx (OR, sp, eq)) in
                (* other transformations do not touch it *)
                MUnsafe (-1, (expr_s e) ^ ";")
            in
            
            [ prev_ne_next; MPrint (-1, str, prev_idx :: next_idx :: es)]

        method mk_init active_expr decls init_stmts =
            let init_locals = find_init_local_vals ctr_ctx decls init_stmts in
            let size_dist_list =
                dom#scatter_abs_vals
                    solver active_expr (List.length init_locals) in
            let mk_option local_vals abs_size =
                let valuation = Hashtbl.create 10 in
                List.iter
                    (fun (var, i) ->
                        Hashtbl.add valuation var i
                    ) local_vals;
                let idx = ctr_ctx#pack_to_const valuation in
                let lhs =
                    BinEx (ARR_ACCESS,
                        Var ctr_ctx#get_ctr, Const idx) in
                MExpr (-1, BinEx (ASGN, lhs, Const abs_size))
            in
            let option_list =
                List.map
                    (fun d -> List.map2 mk_option init_locals d
                    ) size_dist_list
            in
            [mk_nondet_choice option_list]
                @ self#mk_post_asserts active_expr (Const (-1)) (Const 0)

        method mk_counter_update prev_idx next_idx =
            let mk_one tok idx_ex = 
                let ktr_i = self#deref_ctr idx_ex in
                let is_deref = function
                    | BinEx (ARR_ACCESS, _, _) -> true
                    | _ -> false
                in
                let expr_abs_vals =
                    mk_expr_abstraction solver dom is_deref
                        (BinEx (tok, ktr_i, Const 1)) in
                mk_assign_unfolding ktr_i expr_abs_vals
            in
            [mk_one MINUS prev_idx; mk_one PLUS next_idx]

        method keep_assume e = false
    end;;

class vass_funcs dom t_ctx ctr_ctx solver =
    object(self)
        inherit ctr_funcs ctr_ctx 

        (* a free variable delta describing how many processes made a step *)
        val mutable delta = new var "vass_dta"

        method introduced_vars = [delta]

        method mk_pre_loop active_expr =
            [MHavoc (-1, delta);
             MAssume (-1, BinEx (GT, Var delta, Const 0));]

        method mk_pre_asserts active_expr prev_idx next_idx =
            let acc i = BinEx (ARR_ACCESS, Var ctr_ctx#get_ctr, Const i) in
            let add s i =
                if s <> Const 0
                then BinEx (PLUS, acc i, s)
                else acc i
            in
            (* counter are non-negative, non-obvious for an SMT solver! *)
            let all_indices = (range 0 ctr_ctx#get_ctr_dim) in
            let mk_non_neg i = MAssume (-1, BinEx (GE, acc i, Const 0)) in
            (* the sum of counters is indeed the number of processes! *)
            (* though it is preserved in VASS, it is lost in the counter abs. *)
            let sum =
                List.fold_left add (Const 0) (range 0 ctr_ctx#get_ctr_dim) in
            MAssume (-1, BinEx (EQ, active_expr, sum));
            :: (List.map mk_non_neg all_indices)

        method mk_post_asserts active_expr prev_idx next_idx =
            self#mk_pre_asserts active_expr prev_idx next_idx

        method mk_init active_expr decls init_stmts =
            let init_locals = find_init_local_vals ctr_ctx decls init_stmts in
            let has_val valuation =
                let same_var (x, (i: int)) = (i = (Hashtbl.find valuation x)) in
                let same_asgn lst = List.for_all same_var lst in
                try List.exists same_asgn init_locals
                with Not_found -> false
            in
            let indices = ctr_ctx#all_indices_for has_val in
            let sum_fun e i =
                let ctr_ex = BinEx (ARR_ACCESS, Var ctr_ctx#get_ctr, Const i)
                in
                if is_nop e then ctr_ex else BinEx (PLUS, e, ctr_ex)
            in
            let sum_ex = List.fold_left sum_fun (Nop "") indices in
            let sum_eq_n = MAssume (-1, BinEx (EQ, active_expr, sum_ex)) in
            let other_indices =
                List.filter (fun i -> not (List.mem i indices))
                    (range 0 ctr_ctx#get_ctr_dim) in
            let mk_oth i = MAssume (-1, BinEx (EQ, Const 0, sum_fun (Nop "") i))
            in
            let other0 = List.map mk_oth other_indices in
            sum_eq_n :: other0
                @ (self#mk_post_asserts active_expr (Const 0) (Const 0))

        method mk_counter_update prev_idx next_idx =
            (* XXX: use a havoc-like operator here *)
            (* it is very important that we add delta instead of 1 here,
               as it describes a summary of several processes doing the same
               step *)
            let mk_one tok idx_ex =
                let ktr_i = self#deref_ctr idx_ex in
                MExpr (-1, BinEx (ASGN, ktr_i, BinEx (tok, ktr_i, Var delta)))
            in
            [ (*MAssume (-1, BinEx (EQ, Var delta, Const 1));*)
             MAssume (-1, BinEx (GE, self#deref_ctr prev_idx, Const 0));
             mk_one MINUS prev_idx; mk_one PLUS next_idx]

        method keep_assume e = true
    end;;

let do_counter_abstraction t_ctx dom solver ctr_ctx funcs units =
    let atomic_props = Hashtbl.create 10 in
    let replace_assume = function
        | MAssume (id, Var v) as s ->
                begin
                try 
                    if funcs#keep_assume (Var v)
                    then 
                        if v#proc_name = "spec"
                        then MAssume (id, Hashtbl.find atomic_props v#get_name)
                        else s
                    else MSkip id
                with Not_found ->
                    raise (Failure
                        (sprintf "No atomic prop %s found" v#get_name))
                end
        | _ as s -> s
    in
    let counter_guard =
        let make_opt idx =
            let guard =
                (BinEx (NE,
                    BinEx (ARR_ACCESS, Var ctr_ctx#get_ctr, Const idx),
                    Const 0))
            in
            MExpr (-1, guard) :: (* and then assignments *)
                (Hashtbl.fold
                    (fun var value lst -> 
                        MExpr (-1, BinEx (ASGN, Var var, Const value)) :: lst)
                    (ctr_ctx#unpack_from_const idx) [])
        in
        let indices = range 0 ctr_ctx#get_ctr_dim in
        [mk_nondet_choice (List.map make_opt indices)]
    in
    let replace_update active_expr update stmts =
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
        let prev_idx_ex = ctr_ctx#pack_index_expr in
        let next_idx_ex =
            map_vars
                (fun v ->
                    try Var (Hashtbl.find prev_next_pairs v)
                    with Not_found -> Var v
                ) prev_idx_ex in
        let pre_asserts =
            funcs#mk_pre_asserts active_expr prev_idx_ex next_idx_ex in
        let post_asserts =
            funcs#mk_post_asserts active_expr prev_idx_ex next_idx_ex in

        pre_asserts
        @ (funcs#mk_counter_update prev_idx_ex next_idx_ex)
        @ [MUnsafe (-1, "#include \"cegar_post.inc\"")]
        @ post_asserts
        @ new_update
    in
    let replace_comp stmts =
        let rec hack_nsnt = function
            (* XXX: this is a hack saying if we have nsnt + 1,
                then it must be nsnt + delta *)
            | MExpr (id, BinEx (ASGN, Var x, BinEx (PLUS, Var y, Const 1))) as s ->
                if t_ctx#must_hack_expr (Var x) && x#get_name = y#get_name
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
        let replace_assume = function
            | MAssume (id, Var v) as s ->
                    begin
                    try 
                        if funcs#keep_assume (Var v)
                        then 
                            if v#proc_name = "spec"
                            then MAssume (id, Hashtbl.find atomic_props v#get_name)
                            else s
                        else MSkip id
                    with Not_found ->
                        raise (Failure
                            (sprintf "No atomic prop %s found" v#get_name))
                    end
            | _ as s -> s
        in List.map hack_nsnt (List.map replace_assume stmts)
    in
    let xducers = Hashtbl.create 1 in (* transition relations in SMT *)
    let abstract_proc p =
        let body = remove_bad_statements p#get_stmts in
        let skel = extract_skel body in
        let main_lab = mk_uniq_label () in
        let new_init = funcs#mk_init p#get_active_expr skel.decl skel.init in
        let new_update = replace_update p#get_active_expr skel.update body in
        let new_comp = replace_comp skel.comp in
        let new_comp_upd = MAtomic (-1, new_comp @ new_update) in
        let new_loop_body =
            counter_guard
            @ [MIf (-1,
                [MOptGuarded ([new_comp_upd])]);
               MGoto (-1, main_lab)] in
        let new_body = 
            skel.decl
            @ [MUnsafe (-1, "#include \"cegar_decl.inc\"")]
            @ new_init
            @ [MLabel (-1, main_lab)]
            @ skel.loop_prefix
            @ (funcs#mk_pre_loop p#get_active_expr)
            @ [MUnsafe (-1, "#include \"cegar_pre.inc\"")]
            @ new_loop_body
        in
        let new_proc = proc_replace_body p new_body in
        new_proc#set_active_expr (Const 1);
        (* SMT xducer: exactly at this moment we have all information to
           generate a xducer of a process
         *)
        let lirs = (mir_to_lir (new_loop_body @ [MLabel (-1, main_lab)])) in
        let all_vars =
            (ctr_ctx#get_ctr :: t_ctx#get_shared) @ funcs#introduced_vars in
        let cfg = mk_ssa true all_vars t_ctx#get_non_shared (mk_cfg lirs) in
        if may_log DEBUG
        then print_detailed_cfg ("Loop of " ^ p#get_name ^ " in SSA: " ) cfg;
        let transd = cfg_to_constraints cfg in
        Hashtbl.add xducers p#get_name transd;
        Cfg.write_dot (sprintf "ssa_%s.dot" p#get_name) cfg;
        (* end of xducer *)
        new_proc
    in

    let abs_unit = function
    | Proc p ->
            let np = abstract_proc p in
            np#set_provided (BinEx (EQ, Var ctr_ctx#get_spur, Const 0));
            Proc np
    | Stmt (MDeclProp (id, v, PropGlob e) as s) ->
       begin 
            let nd = trans_prop_decl t_ctx ctr_ctx dom solver s in
            match nd with
            | MDeclProp (_, _, PropGlob ne) ->
                Hashtbl.add atomic_props v#get_name ne;
                Stmt (MDeclProp (id, v, PropGlob ne))
            | _ -> Stmt (MSkip id)
       end
    | Stmt (MDeclProp (_, _, _) as d) ->
        Stmt (trans_prop_decl t_ctx ctr_ctx dom solver d)
    | _ as u -> u
    in
    let new_units = List.map abs_unit units in
    let keep_unit = function
        | Stmt (MDecl (_, v, _)) -> not v#is_symbolic
        | Stmt (MAssume (_, _)) -> false
        | Stmt (MSkip _) -> false
        | _ -> true
    in
    let out_units =
        (Stmt (MDecl (-1, ctr_ctx#get_ctr, Nop "")))
        :: (Stmt (MDecl (-1, ctr_ctx#get_spur, Const 0)))
        :: (List.filter keep_unit new_units) in
    (out_units, xducers, atomic_props)
;;

