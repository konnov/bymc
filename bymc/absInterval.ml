open Printf;;

open Cfg;;
open Spin;;
open SpinIr;;
open SpinIrImp;;
open Smt;;
open Analysis;;
open SkelStruc;;
open Accums;;
open Writer;;
open Debug;;

open AbsBasics;;
open VarRole;;

exception Skeleton_not_supported of string;;

(* Context of parametric interval abstraction.
   It collects variable roles over different process prototypes.
 *)
class ['tok] trans_context =
    object(self)
        val mutable globals: var list = []
        val mutable assumps: 'tok expr list = []
        val mutable var_roles: (var, var_role) Hashtbl.t = Hashtbl.create 1
        (* XXX: special hack mode for VASS, shared variables
           treated differently.
           TODO: do it w/o hack after the deadline!
         *)
        val mutable m_hack_shared: bool = false

        (*
          Run a solver prepopulated with a context.
          The callee has to call solver#stop afterwards
         *)
        method run_solver =
            let smt_exprs =
                List.append
                    (List.map var_to_smt self#get_symbolic)
                    (List.map (fun e -> sprintf "(assert %s)" (expr_to_smt e))
                        assumps)
            in
            let solver = new yices_smt in
            solver#start;
            (* solver#set_debug true; *) (* see yices.log *)
            List.iter solver#append smt_exprs;
            solver

        method get_role v = Hashtbl.find var_roles v

        method get_globals = globals
        method set_globals g = globals <- g
        method is_global v =
            try v = (List.find ((=) v) globals)
            with Not_found -> false

        method get_shared =
            List.filter (fun v -> not v#is_symbolic) globals

        method get_non_shared =
            List.filter (fun v -> not (self#is_global v)) (hashtbl_keys var_roles)

        method get_symbolic =
            List.filter (fun v -> v#is_symbolic) globals

        method get_var_roles = var_roles
        method set_var_roles r = var_roles <- r
        method get_assumps = assumps
        method set_assumps a = assumps <- a

        method is_hack_shared = m_hack_shared
        method set_hack_shared b = m_hack_shared <- b

        method must_keep_concrete (e: token expr) = 
            match e with
            | Var v -> m_hack_shared && is_shared_unbounded (self#get_role v)
            | _ -> false

        method var_needs_abstraction (v: var) =
            let r = self#get_role v in
            (not (self#must_keep_concrete (Var v))) && (not (is_bounded r))
    end
;;

(* XXX: copied from spin.mly *)
let rec has_expr_symbolic e =
    match e with
    | Const _ -> true
    | Var v -> v#is_symbolic
    | UnEx (op, se) -> op = UMIN && has_expr_symbolic se
    | BinEx (op, le, re) ->
        (List.mem op [PLUS; MINUS; MULT; DIV; MOD])
            && (has_expr_symbolic le) && (has_expr_symbolic re)
    | _ -> false
;;

let identify_conditions var_roles stmts =
    let is_threshold v e =
        let r = Hashtbl.find var_roles v in
        (r = LocalUnbounded || r = Scratch) && (has_expr_symbolic e)
    in
    let rec on_expr e =
        match e with
        | BinEx(AND, l, r) -> List.append (on_expr l) (on_expr r)
        | BinEx(OR, l, r)  -> List.append (on_expr l) (on_expr r)
        | UnEx(NEG, l)     -> on_expr l
        | BinEx(LT, Var v, e) -> if is_threshold v e then [e] else []
        | BinEx(GE, Var v, e) -> if is_threshold v e then [e] else []
        | BinEx(LE, e, Var v) -> if is_threshold v e then [e] else []
        | BinEx(GT, e, Var v) -> if is_threshold v e then [e] else []
        | BinEx(LE, Var v, e) ->
            if is_threshold v e
            then raise (Skeleton_not_supported "var <= expr")
            else []
        | BinEx(GE, e, Var v) ->
            if is_threshold v e
            then raise (Skeleton_not_supported "expr >= var")
            else []
        | BinEx(GT, Var v, e) ->
            if is_threshold v e
            then raise (Skeleton_not_supported "var > expr")
            else []
        | BinEx(LT, e, Var v) ->
            if is_threshold v e
            then raise (Skeleton_not_supported "expr < var")
            else []
        | _ -> []
    in
    let rec on_stmts sts = match sts with
        | Expr (_, e) :: tl -> List.append (on_expr e) (on_stmts tl)
        | _ :: tl    -> on_stmts tl
        | _ -> []
    in
    let cs = (Const 0) :: (Const 1) :: (on_stmts stmts) in
    (* TODO: simplify and canonize expressions here, i.e.,
       f+1 and 1+f should be the same expression *)

    (* remove duplicates *)
    let tbl = Hashtbl.create 10 in
    List.iter
        (fun c ->
            let s = (expr_s c) in
            if not (Hashtbl.mem tbl s) then Hashtbl.add tbl s c)
        cs;
    Hashtbl.fold (fun text cond lst -> cond :: lst) tbl []
;;

let rec extract_assumptions units =
    match units with
    | Stmt (MAssume (_, e)) :: tl -> e :: (extract_assumptions tl)
    | _ :: tl -> extract_assumptions tl
    | [] -> []
;;

let rec extract_globals units =
    match units with
    | Stmt MDecl (_, v, _) :: tl -> v :: (extract_globals tl)
    | _ :: tl -> extract_globals tl
    | [] -> []
;;

let sort_thresholds solver ctx conds =
    let id_map = Hashtbl.create 10 in
    List.iter (fun c -> Hashtbl.add id_map c (Hashtbl.length id_map)) conds;
    solver#push_ctx;
    let cmp_tbl = Hashtbl.create 10 in
    let compare op c1 c2 =
        if c1 <> c2
        then begin
            let asrt =
                sprintf "(not (%s %s %s))" op (expr_to_smt c1) (expr_to_smt c2)
            in
            solver#append_assert asrt;
            let res = not solver#check in
            if res
            then (Hashtbl.add cmp_tbl
                ((Hashtbl.find id_map c1), (Hashtbl.find id_map c2)) true);
            solver#pop_ctx; solver#push_ctx;
            res
        end
        else false
    in
    let lt c1 c2 = let _ = compare "<" c1 c2 in () in
    List.iter (fun c1 -> List.iter (lt c1) conds) conds;
    let rm_tbl = Hashtbl.create 10 in
    let check_ord c1 c2 = 
        let i1 = (Hashtbl.find id_map c1) and i2 = (Hashtbl.find id_map c2) in
        if i1 <> i2
        then if not (Hashtbl.mem cmp_tbl (i1, i2))
            && not (Hashtbl.mem cmp_tbl (i2, i1))
        then begin
            let m =
                sprintf "No strict order for %s and %s" (expr_s c1) (expr_s c2)
            in
            if compare "<=" c1 c2
            then begin
                printf "%s is subsumed by %s\n" (expr_s c2) (expr_s c1);
                Hashtbl.replace rm_tbl c2 true
            end else if compare "<=" c2 c1
            then begin
                printf "%s is subsumed by %s\n" (expr_s c1) (expr_s c2);
                Hashtbl.replace rm_tbl c1 true
            end else
            raise (Abstraction_error m)
        end
    in
    List.iter (fun c1 -> List.iter (check_ord c1) conds) conds;
    solver#pop_ctx;
    let conds = List.filter (fun c -> not (Hashtbl.mem rm_tbl c)) conds in
    let cmp_using_tbl c1 c2 =
        let i1 = (Hashtbl.find id_map c1) and i2 = (Hashtbl.find id_map c2) in
        if c1 = c2 then 0 else if (Hashtbl.mem cmp_tbl (i1, i2)) then -1 else 1
    in
    List.sort cmp_using_tbl conds
;;

let mk_context units =
    let ctx = new trans_context in
    ctx#set_var_roles (identify_var_roles units);
    log INFO " # Variable roles:";
    let sorted = List.sort cmp_qual_vars (hashtbl_keys ctx#get_var_roles) in
    let print_var_role v =
        let r = Hashtbl.find ctx#get_var_roles v in
        log INFO (sprintf "   %s -> %s" v#qual_name (var_role_s r)) in
    List.iter print_var_role sorted;
    ctx#set_assumps (extract_assumptions units);
    log INFO " # Assumptions:";
    List.iter
        (fun e -> log INFO (sprintf "   assume(%s)" (expr_s e)))
        ctx#get_assumps;
    ctx#set_globals (extract_globals units);
    log INFO " # Globals:";
    List.iter
        (fun v -> log INFO (sprintf "   var %s" v#get_name))
        ctx#get_globals;
    ctx
;;

let mk_domain solver ctx units =
    log INFO "> Extracting an abstract domain...";
    let collect_stmts l = function
        | Proc p -> p#get_stmts @ l
        | _ -> l
    in
    let all_stmts = List.fold_left collect_stmts [] units in
    let conds = identify_conditions ctx#get_var_roles (mir_to_lir all_stmts) in
    let sorted_conds = sort_thresholds solver ctx conds in
    let dom = PiaDom.create sorted_conds in
    dom#print;
    flush stdout;
    dom
;;

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
                let v = new var (sprintf "_arg%d" (Hashtbl.length mapping)) in
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
    let res_var = new var "_res" in
    let expr_w_args = sub expr in
    let vars_used = res_var :: (expr_used_vars expr_w_args) (* i.e. _res; _arg0 *)
    in
    solver#push_ctx;
    (* introduce the variables to the SMT solver *)
    List.iter (solver#append_var_def) vars_used;
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
;;

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
;;

let over_dom ctx = function
    | Var v ->
        begin
            try
                v#is_symbolic || (is_unbounded (ctx#get_role v))
            with Not_found ->
                raise (Abstraction_error (sprintf "No role for %s" v#get_name))
        end

    | _ -> false
;;

let non_symbolic = function
    | Var v -> not v#is_symbolic
    | _ -> false
;;

let var_trait t_ctx v =
    if v#is_symbolic
    then ConstExpr
    else if t_ctx#var_needs_abstraction v
    then AbsExpr
    else ConcExpr
;;

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
    list_to_binex OR (List.map mk_point points_lst)
;;

(* make an abstraction of an arithmetic relation: <, <=, >, >=, ==, != *)
let abstract_arith_rel ctx dom solver atype tok lhs rhs =
    let orig_expr = BinEx (tok, lhs, rhs) in
    let ltrait = get_abs_trait (var_trait ctx) lhs in
    let rtrait = get_abs_trait (var_trait ctx) rhs in
    let mk_eq var abs_val = BinEx (EQ, Var var, Const abs_val) in
    match ltrait, rtrait with
    | ConstExpr, AbsExpr ->
        (* do a single argument abstraction when rhs is var,
           otherwise do the general abstraction *)
        if is_var rhs
        then BinEx (tok, (dom#map_concrete solver lhs), rhs)
        else abstract_pointwise ctx dom solver atype mk_eq orig_expr

    | AbsExpr, ConstExpr ->
        if is_var lhs
        then BinEx (tok, lhs, (dom#map_concrete solver rhs))
        else abstract_pointwise ctx dom solver atype mk_eq orig_expr

    | AbsExpr, AbsExpr ->
        (* general abstraction *)
        abstract_pointwise ctx dom solver atype mk_eq orig_expr

    | ConcExpr, AbsExpr ->
        (* do abstract_pointwise general abstraction, then concretize lhs *)
        let tmp_var = new var "_concX" in
        solver#append_var_def tmp_var;
        let new_expr = (BinEx (tok, Var tmp_var, rhs)) in
        let restore_lhs v abs_val =
            if v == tmp_var
            then dom#expr_is_concretization lhs abs_val
            else BinEx (EQ, Var v, Const abs_val)
        in
        abstract_pointwise ctx dom solver atype restore_lhs new_expr

    | AbsExpr, ConcExpr ->
        let tmp_var = new var "_concX" in
        solver#append_var_def tmp_var;
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
;;

let translate_expr ctx dom solver atype expr =
    let invert_abs_type neg_sign = function
        | ExistAbs -> if neg_sign then UnivAbs else ExistAbs
        | UnivAbs  -> if neg_sign then ExistAbs else UnivAbs
    in
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
            let eff_abs = (invert_abs_type neg_sign atype) in
            abstract_arith_rel ctx dom solver eff_abs eff_op lhs rhs

        | _ -> raise (Abstraction_error
            (sprintf "No abstraction for: %s" (expr_s expr)))
    in
    trans_e false expr
;;

(* The first phase of the abstraction takes place here *)
(* TODO: refactor it, should be simplified *)
let translate_stmt ctx dom solver stmt =
    let rec abs_seq seq = List.fold_right (fun s l -> (abs_stmt s) :: l) seq [] 
    and abs_stmt = function
    | MExpr (id, e) as s ->
        if not (expr_exists (over_dom ctx) e)
        then s (* no domain variables, keep as it is *)
        else begin
            match e with
            | BinEx (ASGN, lhs, rhs) ->
                (* special cases *)
                if ctx#must_keep_concrete lhs
                then s (* XXX: hack shared variables in VASS, keep untouched *)
                else if not (expr_exists non_symbolic rhs)
                (* substitute a constant expression
                   by its abstract value on the right-hand side *)
                then MExpr (id, BinEx (ASGN, lhs, (dom#map_concrete solver rhs)))
                else if is_var rhs
                (* special case: foo = bar; keep untouched *)
                then s
                (* the general case: find all possible abstract values of the rhs *)
                else let expr_abs_vals =
                        mk_expr_abstraction solver dom
                            (fun e -> is_var e && not (has_expr_symbolic e)) rhs in
                    (mk_assign_unfolding lhs expr_abs_vals)

            | _ ->
                    solver#push_ctx;
                    let out = MExpr (id, translate_expr ctx dom solver ExistAbs e) in
                    solver#pop_ctx;
                    out
        end                

    | MAtomic (id, seq) -> MAtomic (id, (abs_seq seq))

    | MD_step (id, seq) -> MD_step (id, (abs_seq seq))

    | MIf (id, opts) ->
        let abs_opt = function
            | MOptGuarded seq -> MOptGuarded (abs_seq seq)
            | MOptElse seq -> MOptElse (abs_seq seq)
        in
        MIf (id, List.map abs_opt opts)

    | _ as s -> s
    in
    abs_stmt stmt 
;;

let trans_prop_decl ctx dom solver decl_expr =
    let tr_e e =
        let used_vars = expr_used_vars e in
        let locals = List.filter (fun v -> v#proc_name <> "") used_vars in
        solver#push_ctx;
        List.iter solver#append_var_def locals;
        List.iter solver#append_var_def ctx#get_shared;
        let abs_ex = translate_expr ctx dom solver UnivAbs e in
        solver#pop_ctx;
        abs_ex
    in
    match decl_expr with
        | MDeclProp (id, v, PropAll e) ->
            if not (expr_exists (over_dom ctx) e)
            then decl_expr
            else MDeclProp (id, v, PropAll (tr_e e))
        | MDeclProp (id, v, PropSome e) ->
            if not (expr_exists (over_dom ctx) e)
            then decl_expr
            else MDeclProp (id, v, PropSome (tr_e e))
        | MDeclProp (id, v, PropGlob e) ->
            if not (expr_exists (over_dom ctx) e)
            then decl_expr
            else MDeclProp (id, v, PropGlob (tr_e e))
        | _ -> decl_expr
;;

let do_interval_abstraction ctx dom solver units = 
    let on_unit = function
        | Proc p ->
            solver#push_ctx;
            List.iter solver#append_var_def p#get_locals;
            List.iter solver#append_var_def ctx#get_shared;
            let body = List.map (translate_stmt ctx dom solver) p#get_stmts in
            log DEBUG (sprintf " -> Abstract skel of proctype %s\n" p#get_name);
            List.iter (fun s -> log DEBUG (mir_stmt_s s)) body;
            solver#pop_ctx;
            Proc (proc_replace_body p body)

        | Stmt (MDeclProp (_, _, _) as d) ->
            Stmt (trans_prop_decl ctx dom solver d)

        | _ as u -> u
    in
    List.map on_unit units
;;

