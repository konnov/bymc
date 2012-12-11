open Printf

open Cfg
open Spin
open SpinIr
open SpinIrImp
open Smt
open Analysis
open SkelStruc
open Accums
open Writer
open Debug

open AbsBasics
open VarRole


(*
  Abstraction of an expression over a variable and symbolic parameters.
  is_leaf_fun evaluates an expression to true if no further expansion of
  expr must be performed. Such an expression is replaced by a variable _argX
  and after abstraction restored back.
  
  XXX: the _res variable looks ad hoc.
 *)
let mk_expr_abstraction solver dom is_leaf_fun expr =
    (* replace leaf expressions with a variable _argI *)
    let mapping = Hashtbl.create 1 in
    let rec sub e =
        if is_leaf_fun e
        then if Hashtbl.mem mapping e
            then Var (Hashtbl.find mapping e)
            else begin
                let v = new_var (sprintf "_arg%d" (Hashtbl.length mapping)) in
                Hashtbl.add mapping e v;
                Var v
            end
        else match e with
            | UnEx (t, l) -> UnEx (t, sub l)
            | BinEx (t, l, r) -> BinEx (t, sub l, sub r)
            | _ as e -> e
    in
    (* FIXME: the number of variables is limited by two now for no reason *)
    assert ((Hashtbl.length mapping) <= 1);
    let res_var = new_var "_res" in
    let expr_w_args = sub expr in
    let vars_used = res_var :: (expr_used_vars expr_w_args) (* i.e. _res; _arg0 *)
    in
    solver#push_ctx;
    (* introduce the variables to the SMT solver *)
    let append_def v =
        solver#append_var_def v (new data_type SpinTypes.TINT) in
    List.iter append_def vars_used;
    (* find matching combinations of _res and _arg0 *)
    let matching_vals =
        (dom#find_abs_vals ExistAbs solver (BinEx (EQ, Var res_var, expr_w_args))) in
    solver#pop_ctx;
    let inv_map = hashtbl_inverse mapping in
    (* list of pairs of abstract values for ((_res, d'), (e(_arg0), d'')) *)
    let map_vars_back (var, abs_val) =
        if Hashtbl.mem inv_map var
        then (Hashtbl.find inv_map var, abs_val)
        else (Var var, abs_val)
    in
    List.map (List.map map_vars_back) matching_vals


(* XXX: refactor *)
let mk_assign_unfolding lhs (expr_abs_vals : (token expr * int) list list) =
    let is_out_var = function
        | Var v -> "_res" = v#get_name (* XXX: magic name! *)
        | _ -> false
    in
    (* create an if/fi enumerating all combinations of lhs and rhs *)
    let labs = List.map (fun _ -> mk_uniq_label ()) expr_abs_vals in
    let guarded_actions =
        List.map2 (fun lab abs_tuple ->
            let guard = List.fold_left
                (fun lits (ex, abs_val) ->
                    if not (is_out_var ex)
                    then let lit = BinEx (EQ, ex, Const abs_val) in
                        if is_nop lits then lit else BinEx (AND, lits, lit)
                    else lits (* skip this var *))
                (Nop "") abs_tuple
            in
            let assigns = List.fold_left
                (fun seq (ex, abs_val) ->
                    if is_out_var ex
                    then MExpr (-1, BinEx (ASGN, lhs, Const abs_val)) :: seq
                    else seq (* skip condition variables *) )
                [] abs_tuple
            in
            MOptGuarded (MExpr (-1, guard) :: assigns)
        ) labs expr_abs_vals
    in
    MIf (-1, guarded_actions)


let over_dom (roles: var_role_tbl) = function
    | Var v ->
        begin
            try v#is_symbolic || (is_unbounded (roles#get_role v))
            with Not_found ->
                raise (Abstraction_error (sprintf "No role for %s" v#get_name))
        end

    | _ -> false


let var_trait t_ctx v =
    if v#is_symbolic
    then ConstExpr
    else if t_ctx#var_needs_abstraction v
    then AbsExpr
    else ConcExpr


let refine_var_type ctx dom roles type_tab new_type_tab v =
    let bounds = function
        | BoundedInt (a, b) -> (a, b + 1)
        | _ -> raise (Abstraction_error ("No bound for " ^ v#get_name))
    in
    let new_type =
        let vrole = roles#get_role v in
        if ctx#var_needs_abstraction v
        then begin
            let tp = new data_type SpinTypes.TINT in
            tp#set_range 0 (dom#length + 1);
            tp
        end else if is_bounded vrole
        then begin
            let l, r = bounds vrole in
            let tp = new data_type SpinTypes.TINT in
            tp#set_range l (r + 1);
            tp
        end else type_tab#get_type v#id
    in
    new_type_tab#set_type v#id new_type

(*
 Translate an arithmetic comparison to a pointwise comparison of
 abstract values. Find the vectors of abstract values that match
 a symbolic expression (using either an existential or universal
 abstraction). Then construct a disjunctive normal form on the
 conditions.
     
 Create a disjunction of conjunctions enumerating abstract values:
    (vx == 0) && (vy == 1) || (vx == 2) && (vy == 0)
*)
let abstract_pointwise ctx dom solver atype coord_point_fun symb_expr =
    solver#comment ("abstract_pointwise: " ^ (expr_s symb_expr));
    let mk_eq (var, abs_val) = coord_point_fun var abs_val in
    let mk_point point_tuple = list_to_binex AND (List.map mk_eq point_tuple)
    in
    let points_lst = (dom#find_abs_vals atype solver symb_expr) in
    if points_lst <> []
    then list_to_binex OR (List.map mk_point points_lst)
    else Const 0 (* false *)


(* make an abstraction of an arithmetic relation: <, <=, >, >=, ==, != *)
let abstract_arith_rel ctx dom solver atype tok lhs rhs =
    let orig_expr = BinEx (tok, lhs, rhs) in
    let ltrait = get_abs_trait (var_trait ctx) lhs in
    let rtrait = get_abs_trait (var_trait ctx) rhs in
    let mk_eq var abs_val = BinEx (EQ, Var var, Const abs_val) in
    match ltrait, rtrait with
    | ConstExpr, AbsExpr ->
        (* XXX: this optimization conflicts with complex atomic expressions
            like (all(P:x < T + 1)) *)
        (* do a single argument abstraction when rhs is var,
           otherwise do the general abstraction *)
        (*if is_var rhs
        then BinEx (tok, (dom#map_concrete solver lhs), rhs)
        else*)
        abstract_pointwise ctx dom solver atype mk_eq orig_expr

    | AbsExpr, ConstExpr ->
        (*if is_var lhs
        then BinEx (tok, lhs, (dom#map_concrete solver rhs))
        else*)
        abstract_pointwise ctx dom solver atype mk_eq orig_expr

    | AbsExpr, AbsExpr ->
        (* general abstraction *)
        abstract_pointwise ctx dom solver atype mk_eq orig_expr

    | ConcExpr, AbsExpr ->
        (* do abstract_pointwise general abstraction, then concretize lhs *)
        let tmp_var = new_var "_concX" in
        solver#append_var_def tmp_var (new data_type SpinTypes.TINT);
        let new_expr = (BinEx (tok, Var tmp_var, rhs)) in
        let restore_lhs v abs_val =
            if v == tmp_var
            then dom#expr_is_concretization lhs abs_val
            else BinEx (EQ, Var v, Const abs_val)
        in
        abstract_pointwise ctx dom solver atype restore_lhs new_expr

    | AbsExpr, ConcExpr ->
        let tmp_var = new_var "_concX" in
        solver#append_var_def tmp_var (new data_type SpinTypes.TINT);
        let new_expr = (BinEx (tok, lhs, Var tmp_var)) in
        let restore_rhs v abs_val =
            if v == tmp_var
            then dom#expr_is_concretization rhs abs_val
            else BinEx (EQ, Var v, Const abs_val)
        in
        abstract_pointwise ctx dom solver atype restore_rhs new_expr

    | ConcExpr, ConcExpr
    | ConcExpr, ConstExpr
    | ConstExpr, ConcExpr
    | ShadowExpr, ShadowExpr -> 
        (* keep it *)
        BinEx (tok, lhs, rhs)
    | _ ->
        let m = (sprintf "Mixture of abstract and concrete variables in %s"
                (expr_s (BinEx (tok, lhs, rhs)))) in
        raise (Abstraction_error m)


let translate_expr ctx dom solver atype expr =
    let rec trans_e neg_sign = function
        (* boolean combination of arithmetic constraints *)
        | BinEx (AND, lhs, rhs) ->
            BinEx ((if neg_sign then OR else AND),
                (trans_e neg_sign lhs), (trans_e neg_sign rhs))
        | BinEx (OR, lhs, rhs) ->
            BinEx ((if neg_sign then AND else OR),
                (trans_e neg_sign lhs), (trans_e neg_sign rhs))
        (* push negations inside as (as in Kesten, Pnueli. Cornerstones...) *)
        | UnEx  (NEG, lhs) ->
            trans_e (not neg_sign) lhs

        (* arithmetic comparisons *)
        | BinEx (LT, lhs, rhs)
        | BinEx (LE, lhs, rhs)
        | BinEx (GT, lhs, rhs)
        | BinEx (GE, lhs, rhs)
        | BinEx (EQ, lhs, rhs)
        | BinEx (NE, lhs, rhs) as e ->
            let eff_op = if neg_sign
            then (not_of_arith_rel (op_of_expr e))
            else (op_of_expr e) in
            abstract_arith_rel ctx dom solver atype eff_op lhs rhs

        | _ -> raise (Abstraction_error
            (sprintf "No abstraction for: %s" (expr_s expr)))
    in
    trans_e false expr


(* The first phase of the abstraction takes place here *)
(* TODO: refactor it, should be simplified *)
let translate_stmt solver caches type_tab new_type_tab stmt =
    let ctx = caches#get_analysis#get_pia_data_ctx in
    let roles = caches#get_analysis#get_var_roles in
    let dom = caches#get_analysis#get_pia_dom in
    let rec abs_seq seq = List.fold_right (fun s l -> (abs_stmt s) :: l) seq [] 
    and abs_stmt = function
    | MExpr (id, e) as s ->
        if not (expr_exists (over_dom roles) e)
        then s (* no domain variables, keep as it is *)
        else begin
            match e with
            | BinEx (ASGN, lhs, rhs) ->
                (* special cases *)
                if ctx#must_keep_concrete lhs
                then s (* XXX: hack shared variables in VASS, keep untouched *)
                else if not (expr_exists not_symbolic rhs)
                (* substitute a constant expression
                   by its abstract value on the right-hand side *)
                then MExpr (id, BinEx (ASGN, lhs, (dom#map_concrete solver rhs)))
                else if is_var rhs
                (* special case: foo = bar; keep untouched *)
                then s
                (* the general case: find all possible abstract values of the rhs *)
                else let expr_abs_vals =
                        mk_expr_abstraction solver dom
                            (fun e -> is_var e && not_symbolic e) rhs in
                    (mk_assign_unfolding lhs expr_abs_vals)

            | _ ->
                    solver#push_ctx;
                    let out = MExpr (id, translate_expr ctx dom solver ExistAbs e) in
                    solver#pop_ctx;
                    out
        end                

    | MAtomic (id, seq) -> MAtomic (id, (abs_seq seq))

    | MD_step (id, seq) -> MD_step (id, (abs_seq seq))

    | MIf (id, opts) as if_s ->
        (* Abstraction of options may lead to non-deterministic choices, even if
            the original options were mutually exclusive. Else option must be
            translated into the explicit negation of other guards and then
            abstracted. Otherwise, the abstract relation does not simulate the
            original program (the abstract conditions are not overapproximations).
         *)
        let get_guard accum = function
            (* we expect guards to be free of side-effects, if there is an
              'else' option. Otherwise, we cannot abstract 'else' properly *)
            | MOptGuarded ((MExpr (_, g)) :: tl) ->
                if (is_side_eff_free g)
                then g :: accum
                else raise (Abstraction_error
                    (sprintf "The guard '%s' may have a side effect (how to treat 'else'?)" (expr_s g)))
            | MOptGuarded (s :: tl) ->
                raise (Abstraction_error
                    ("Expected an expression, found: " ^ (mir_stmt_s s)))
            | MOptGuarded [] ->
                raise (Abstraction_error
                    ("Met an empty option in: " ^ (mir_stmt_s if_s)))
            | MOptElse _ -> accum
        in
        let abs_opt = function
            | MOptGuarded seq ->
                MOptGuarded (abs_seq seq)
            | MOptElse seq ->
                (* all guards are evaluated to false *)
                let guards = List.fold_left get_guard [] opts in
                let noguard = UnEx(NEG, list_to_binex OR guards) in
                MOptGuarded (abs_seq (MExpr (-1, noguard) :: seq))
        in
        MIf (id, List.map abs_opt opts)

    | MDecl (id, v, e) ->
        refine_var_type ctx dom roles type_tab new_type_tab v;

        MDecl (id, v, (dom#map_concrete solver e))

    | _ as s -> s
    in
    abs_stmt stmt 

(* 
  Abstract atomic expressions. We produce two types of expressions:
  universally abstracted and existentially abstracted.
  See our TACAS submission (or Pnueli, Zuck 2001) on that.
 *)
let rec trans_prop_decl solver caches prog atype atomic_expr =
    let ctx = caches#get_analysis#get_pia_data_ctx in
    let dom = caches#get_analysis#get_pia_dom in
    let roles = caches#get_analysis#get_var_roles in
    let tr_e e =
        let used_vars = expr_used_vars e in
        let locals = List.filter (fun v -> v#proc_name <> "") used_vars in
        let append_def v =
            solver#append_var_def v (Program.get_type prog v) in
        solver#push_ctx;
        List.iter append_def locals;
        List.iter append_def (Program.get_shared prog);
        let abs_ex = translate_expr ctx dom solver atype e in
        solver#pop_ctx;
        abs_ex
    in
    let drop_quantifier_if_const = function
        | PropAll (Const i as e) -> PropGlob e
        | PropSome (Const i as e) -> PropGlob e
        | _ as qe -> qe
    in
    let rec tr_atomic = function
        | PropAll e ->
            if not (expr_exists (over_dom roles) e)
            then atomic_expr
            else drop_quantifier_if_const (PropAll (tr_e e))
        | PropSome e ->
            if not (expr_exists (over_dom roles) e)
            then atomic_expr
            else drop_quantifier_if_const (PropSome (tr_e e))
        | PropGlob e ->
            if not (expr_exists (over_dom roles) e)
            then atomic_expr
            else PropGlob (tr_e e)
        | PropAnd (l, r) ->
            PropAnd (tr_atomic l, tr_atomic r)
        | PropOr (l, r) ->
            PropOr (tr_atomic l, tr_atomic r)
    in
    tr_atomic atomic_expr


let trans_ltl_form new_type_tab name f =
    let inv atype = if atype = UnivAbs then ExistAbs else UnivAbs in
    let rec tr_f atype = function
    | Var v ->
        let nv = if atype = UnivAbs
            then new_var (v#get_name ^ "_univ")
            else new_var (v#get_name ^ "_exst") in
        new_type_tab#set_type v#id (new data_type SpinTypes.TPROPOSITION);
        Var nv
    | BinEx(AND, l, r) ->
        BinEx(AND, tr_f atype l, tr_f atype r)
    | BinEx(OR, l, r) ->
        BinEx(OR, tr_f atype l, tr_f atype r)
    | BinEx(IMPLIES, l, r) ->
        BinEx(IMPLIES, tr_f (inv atype) l, tr_f atype r)
    | BinEx(EQUIV, l, r) ->
        BinEx(EQUIV, tr_f atype l, tr_f atype r)
    | BinEx(UNTIL, l, r) ->
        BinEx(UNTIL, tr_f atype l, tr_f atype r)
    | BinEx(RELEASE, l, r) ->
        BinEx(RELEASE, tr_f atype l, tr_f atype r)
    | BinEx(WEAK_UNTIL, l, r) ->
        BinEx(WEAK_UNTIL, tr_f atype l, tr_f atype r)
    | UnEx(NEG, g) ->
        UnEx(NEG, tr_f (inv atype) g)
    | UnEx(ALWAYS, g) ->
        UnEx(ALWAYS, tr_f atype g)
    | UnEx(EVENTUALLY, g) ->
        UnEx(EVENTUALLY, tr_f atype g)
    | UnEx(NEXT, _) -> raise (Abstraction_error "Don't use nexttime!")
    | _ as e -> raise (Abstraction_error ("Not an LTL formula: " ^ (expr_s e)))
    in
    if Str.string_match (Str.regexp_string "fairness") name 0
    then tr_f ExistAbs f
    else tr_f UnivAbs f


let do_interval_abstraction solver caches prog = 
    let type_tab = Program.get_type_tab prog in
    let new_type_tab = type_tab#copy in
    let abstract_proc p =
        let add_def v =
            solver#append_var_def v (type_tab#get_type v#id) in
        solver#push_ctx;
        List.iter add_def p#get_locals;
        List.iter add_def (Program.get_shared prog);
        let body = List.map
            (translate_stmt solver caches type_tab new_type_tab) p#get_stmts in
        log DEBUG (sprintf " -> Abstract skel of proctype %s\n" p#get_name);
        List.iter (fun s -> log DEBUG (mir_stmt_s s)) body;
        solver#pop_ctx;
        proc_replace_body p body
    in
    let abstract_atomic name ae map =
        let univ = trans_prop_decl solver caches prog UnivAbs ae in
        let ex = trans_prop_decl solver caches prog ExistAbs ae in
        if Ltl.is_invariant_atomic name
        then Program.StringMap.add name ex map
        else Program.StringMap.add (name ^ "_exst") ex
                (Program.StringMap.add (name ^ "_univ") univ map)
    in
    let new_procs = List.map abstract_proc (Program.get_procs prog) in
    let new_atomics =
        Program.StringMap.fold
            abstract_atomic (Program.get_atomics prog) Program.StringMap.empty
    in
    let new_forms = Program.StringMap.mapi
        (trans_ltl_form new_type_tab) (Program.get_ltl_forms prog) in
    let abs_shared shared_var =
        let ctx = caches#get_analysis#get_pia_data_ctx in
        let dom = caches#get_analysis#get_pia_dom in
        let roles = caches#get_analysis#get_var_roles in
        refine_var_type ctx dom roles type_tab new_type_tab shared_var;
        shared_var
    in
    let new_shared = List.map abs_shared (Program.get_shared prog) in
    (Program.set_shared new_shared
        (Program.set_type_tab new_type_tab
        (Program.set_ltl_forms new_forms
        (Program.set_atomics new_atomics (Program.set_procs new_procs prog)))))

