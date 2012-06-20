open Printf;;

open Accums;;
open Spin;;
open Spin_ir;;
open Spin_ir_imp;;
open Smt;;
open Analysis;;
open Skel_struc;;

open AbsInterval;;

class ctr_abs_ctx dom t_ctx =
    object(self)
        val mutable pc_var: var = t_ctx#find_pc
        val mutable pc_size = 0
        val mutable ctr_var = new var "ktr"
        val mutable local_vars = []
        
        initializer
            pc_size <-
                (match t_ctx#get_role t_ctx#find_pc with
                | BoundedInt (a, b) -> b - a + 1
                | _ -> raise (Abstraction_error "pc variable is not bounded"));
            local_vars <- Hashtbl.fold
                (fun v r lst -> if is_local_unbounded r then v :: lst else lst)
                t_ctx#get_var_roles [];
            ctr_var#set_isarray true;
            ctr_var#set_num_elems
                ((List.length local_vars) * dom#length * pc_size)
           
        method get_pc = pc_var
        method get_pc_size = pc_size
        method get_locals = local_vars
        method get_ctr = ctr_var
        method get_ctr_dim =
            ((List.length local_vars) * dom#length * pc_size)

        method unpack_const i =
            let valuation = Hashtbl.create ((List.length local_vars) + 1) in
            Hashtbl.add valuation pc_var (i mod pc_size);
            let _ =
                List.fold_left
                    (fun j var ->
                        Hashtbl.add valuation var (j mod dom#length);
                        j / dom#length)
                    (i / pc_size) local_vars in
            valuation

        method pack_index_expr =
            let ex =
                List.fold_left
                    (fun subex var ->
                        if subex = Nop
                        then Var var
                        else BinEx (PLUS,
                            BinEx (MULT, subex, Const dom#length),
                            Var var)
                    ) Nop (List.rev local_vars)
            in
            BinEx (PLUS, BinEx (MULT, ex, Const pc_size), Var pc_var)

        method pack_vals_to_index valuation =
            let get_val var =
                try
                    Hashtbl.find valuation var
                with Not_found ->
                    raise (Failure
                        (sprintf "Valuation of %s not found" var#get_name))
            in
            let idx = List.fold_left
                (fun sum var -> (sum * dom#length) + (get_val var)
                ) 0 (List.rev local_vars)
            in
            (idx * pc_size + (get_val pc_var))

        method all_indices_for check_val_fun =
            let has_v i = (check_val_fun (self#unpack_const i)) in
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
            let ke = BinEx (ARRAY_DEREF, Var ctr_ctx#get_ctr, Const idx) in
            if e = Nop
            then BinEx (tok, ke, Const 0)
            else BinEx (sep, e, BinEx (tok, ke, Const 0)) in
        List.fold_left add_cons Nop indices
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
            raise (Abstraction_error
                (sprintf "Don't know how to do counter abstraction for %s"
                    (expr_s e)))
    in
    match decl_expr with
        | MDeclProp (id, v, PropAll e) ->
            MDeclProp (id, v, PropGlob (t_e mk_all e))
        | MDeclProp (id, v, PropSome e) ->
            MDeclProp (id, v, PropGlob (t_e mk_some e))
        | _ -> decl_expr
;;


let do_counter_abstraction t_ctx dom solver units =
    let ctr_ctx = new ctr_abs_ctx dom t_ctx in
    let deref_ctr e =
        BinEx (ARRAY_DEREF, Var ctr_ctx#get_ctr, e)
    in
    let mk_print_stmt prev_idx next_idx =
        let n = ctr_ctx#get_ctr_dim in
        let m = List.length t_ctx#get_shared in
        let str = sprintf "{%%d->%%d:%s}\\n"
            (String.concat "," (Accums.n_copies (n + m) "%d")) in
        let mk_deref i = deref_ctr (Const i) in
        let es = (List.map mk_deref (range 0 n))
            @ (List.map (fun v -> Var v) t_ctx#get_shared) in
        MPrint (-1, str, prev_idx :: next_idx :: es)
    in
    let counter_guard =
        let make_opt idx =
            let guard =
                (BinEx (GT,
                    BinEx (ARRAY_DEREF, Var ctr_ctx#get_ctr, Const idx),
                    Const 0))
            in
            MExpr (-1, guard) :: (* and then assignments *)
                (Hashtbl.fold
                    (fun var value lst -> 
                        MExpr (-1, BinEx (ASGN, Var var, Const value)) :: lst)
                    (ctr_ctx#unpack_const idx) [])
        in
        let indices = range 0 ctr_ctx#get_ctr_dim in
        [mk_nondet_choice (List.map make_opt indices)]
    in
    let replace_init active_expr decls init_stmts =
        (* TODO: simplify/refactor *)
        printf "\n\nINIT PART\n";
        List.iter
            (fun s -> printf "%s\n" (stmt_s s))
            (mir_to_lir (decls @ init_stmts));
        let init_cfg = Cfg.mk_cfg (mir_to_lir (decls @ init_stmts)) in
        let int_roles =
            visit_cfg (visit_basic_block transfer_roles)
                join_int_roles init_cfg (mk_bottom_val ()) in
        let init_sum =
            join_all_locs join_int_roles (mk_bottom_val ()) int_roles in
        let mk_prod left right =
            if left = []
            then List.map (fun x -> [x]) right
            else List.concat
                (List.map (fun r -> List.map (fun l -> l @ [r]) left) right) in
        let init_locals =
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
                ) [] (ctr_ctx#get_pc :: ctr_ctx#get_locals)
        in
        let size_dist_list =
            dom#scatter_abs_vals solver active_expr (List.length init_locals) in
        let option_list =
            List.map
                (fun dist ->
                    List.map2
                        (fun local_vals abs_size ->
                            let valuation = Hashtbl.create (List.length dist) in
                            List.iter
                                (fun (var, i) ->
                                    Hashtbl.add valuation var i
                                ) local_vals;
                            let idx = ctr_ctx#pack_vals_to_index valuation in
                            let lhs =
                                BinEx (ARRAY_DEREF,
                                    Var ctr_ctx#get_ctr, Const idx) in
                            MExpr (-1, BinEx (ASGN, lhs, Const abs_size))
                        ) init_locals dist
                ) size_dist_list
        in
        [mk_nondet_choice option_list; mk_print_stmt (Const 0) (Const 0)]
        (*
        List.iter
            (fun d -> 
                printf "init_distr:\n";
                List.iter2
                    (fun locals count ->
                        printf "   %d -> " count;
                        List.iter
                            (fun (v, i) -> printf "%s = %d; " v#get_name i)
                            locals;
                        printf "\n";
                    ) init_locals d
            ) size_dist_list;
        *)
    in
    let replace_update update stmts =
        (* all local variables should be reset to 0 *)
        let new_update =
            List.map
                (function
                    | MExpr (_1, BinEx (ASGN, Var var, rhs)) as s ->
                        begin
                            match t_ctx#get_role var with
                            | LocalUnbounded
                            | BoundedInt (_, _) ->
                                MExpr (-1, BinEx (ASGN, Var var, Const 0))
                            | _ -> s
                        end
                    | _ as s -> s
                ) update
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
        let mk_ctr_ex idx_ex tok =
            let ktr_i = deref_ctr idx_ex in
            let expr_abs_vals =
                mk_expr_abstraction solver dom
                    (function | BinEx (ARRAY_DEREF, _, _) -> true | _ -> false)
                    (BinEx (tok, ktr_i, Const 1)) in
            [mk_assign_unfolding ktr_i expr_abs_vals]
        in
        let print_stmt = mk_print_stmt prev_idx_ex next_idx_ex in
        (mk_ctr_ex prev_idx_ex MINUS)
            @ (mk_ctr_ex next_idx_ex PLUS)
            @ [print_stmt]
            @ new_update
    in
    let abstract_proc p =
        let body = remove_bad_statements p#get_stmts in
        let skel = extract_skel body in
        let main_lab = mk_uniq_label () in
        let new_init =
            replace_init p#get_active_expr skel.decl skel.init
        in
        let new_update = replace_update skel.update body in
        let new_comp_upd = MAtomic (-1, skel.comp @ new_update) in
        let new_body = 
            skel.decl @ new_init @ [MLabel (-1, main_lab)]
            @ counter_guard @
            [MIf (-1,
                [MOptGuarded ([(*skel.guard; *) new_comp_upd]);
                 MOptGuarded [MExpr (-1, Nop)]]);
             MGoto (-1, main_lab)]
        in
        let new_proc = proc_replace_body p new_body in
        new_proc#set_active_expr (Const 1);
        new_proc
    in
    let abs_unit = function
        | Proc p ->
            Proc (abstract_proc p)
        | Stmt (MDeclProp (_, _, _) as d) ->
            Stmt (trans_prop_decl t_ctx ctr_ctx dom solver d)
        | _ as u -> u
    in
    let new_units = List.map abs_unit units in
    let keep_unit = function
        | Stmt (MDecl (_, v, _)) -> not v#is_symbolic
        | Stmt (MAssume (_, _)) -> false
        | _ -> true
    in
    (Stmt (MDecl (-1, ctr_ctx#get_ctr, Nop)))
        :: (List.filter keep_unit new_units)
;;

