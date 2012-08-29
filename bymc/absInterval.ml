open Printf;;

open Cfg;;
open Spin;;
open Spin_ir;;
open Spin_ir_imp;;
open Smt;;
open Analysis;;
open SkelStruc;;
open Accums;;
open Writer;;
open Debug;;

exception Skeleton_not_supported of string;;
exception Abstraction_error of string;;

type var_role =
    BoundedInt of int * int | SharedUnbounded | LocalUnbounded | Scratch;;

let var_role_s r =
    match r with
    | BoundedInt (a, b) -> sprintf "bound[%d, %d]" a b
    | SharedUnbounded -> "shared-unbound"
    | LocalUnbounded -> "local-unbound"
    | Scratch -> "scratch"
;;

let is_unbounded = function
    | SharedUnbounded
    | LocalUnbounded -> true
    | _ -> false
;;

let is_bounded = function
    | BoundedInt (_, _) -> true
    | _ -> false
;;

let is_local_unbounded = function
    | LocalUnbounded -> true
    | _ -> false
;;

let is_shared_unbounded = function
    | SharedUnbounded -> true
    | _ -> false
;;

(* XXX: it works only for one process prototype *)
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
                    (List.map var_to_smt globals)
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
            try
                v = (List.find ((=) v) globals)
            with Not_found ->
                false

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

        method must_hack_expr (e: token expr) = 
            match e with
            | Var v -> m_hack_shared && is_shared_unbounded (self#get_role v)
            | _ -> false
    end
;;

exception Found of int;;

type abs_type = ExistAbs | UnivAbs;;

class abs_domain conds_i =
    object(self)
        val mutable conds = conds_i      (* thresholds *)
        (* triples of (abstract value, left cond, right cond) *)
        val mutable cond_intervals = []
        val mutable val_map = Hashtbl.create 10 (* from a cond to a value *)

        method print =
            log INFO " # Abstract domain:";
            Hashtbl.iter
                (fun c i -> log INFO (sprintf "   d%d -> %s" i (expr_s c)))
                val_map
        
        initializer
            List.iter
                (fun c -> Hashtbl.add val_map c (Hashtbl.length val_map))
                conds;
            let _, tuples =
                List.fold_left (fun (i, l) (a, b) -> (i + 1, (i, a, b) :: l))
                    (0, [])
                    (List.combine conds (List.append (List.tl conds) [Nop ""]))
            in
            cond_intervals <- tuples

        method length = List.length conds

        method map_concrete (solver: yices_smt) (symb_expr: 't expr) =
            try
                List.iter
                    (fun (_, l, r) ->
                        solver#push_ctx;
                        solver#append_assert
                            (expr_to_smt (BinEx (GE, symb_expr, l)));
                        if not_nop r
                        then solver#append_assert
                            (expr_to_smt (BinEx (LT, symb_expr, r)));
                        let sat = solver#check in
                        solver#pop_ctx;
                        if sat then raise (Found (Hashtbl.find val_map l));
                    ) cond_intervals;
                raise (Abstraction_error
                    (sprintf "No abstract value for %s" (expr_s symb_expr)))
            with Found i ->
                (Const i: Spin.token expr)

        method concretize exp abs_val =
            let (_, l, r) =
                List.find (fun (a, _, _) -> a = abs_val) cond_intervals in
            let left = BinEx (GE, exp, l) in
            if not_nop r
            then BinEx (AND, left, BinEx (LT, exp, r))
            else left

        method find_abs_vals
                (at: abs_type) (solver: yices_smt) (symb_expr: 't expr)
                : (Spin_ir.var * int) list list =
            let used = expr_used_vars symb_expr in
            if (List.length used) <> 2
            (* XXX: nothing prevents us from handling multiple variables *)
            then raise (Abstraction_error
                (sprintf "Expression %s must have two free variables"
                    (expr_s symb_expr)))
            else
            (* enumerate all possible abstract pairs that have a concretization
               satisfying symb_expr
             *)
            begin
                let append_cons var (i, l, r) =
                    solver#append_assert
                        (expr_to_smt (BinEx (GE, Var var, l)));
                    if not_nop r
                    then solver#append_assert
                        (expr_to_smt (BinEx (LT, Var var, r)))
                in
                (* TODO: refactor, it is so complicated! *)
                solver#push_ctx;
                let matching_tuples = List.fold_left
                    (fun lst triples (* of (abs_val, lcond, rcond) *) ->
                        solver#push_ctx;
                        List.iter2 append_cons used triples;
                        let satisfies =
                            if at = ExistAbs
                            then begin
                                solver#append_assert (expr_to_smt symb_expr);
                                solver#check
                            end else begin
                                let neg = UnEx (NEG, symb_expr) in
                                solver#append_assert (expr_to_smt neg);
                                not (solver#check)
                            end
                        in
                        solver#pop_ctx;
                        if satisfies
                        then (List.map2
                            (fun var (i, _, _) -> (var, i)) used triples)
                            :: lst
                        else lst
                    ) [] (Accums.mk_product cond_intervals 2)
                in
                solver#pop_ctx;
                matching_tuples (* now pairs *)
            end

        (*
          distribute n abstract values x_i over the abstract domain s.t.
          sum_{i=1}^n \gamma(x_i) = num_active_processes
         *)
        method scatter_abs_vals (solver: yices_smt)
                (num_expr: 't expr) (n: int) : int list list =
            if n > 4 (* the magic number which means explosion of variants *)
            then raise (Abstraction_error "scatter_abs_vals for n > 4");
            
            let combinations = (Accums.mk_product cond_intervals n) in
            let sat_triples_list = List.filter
                (fun comb ->
                    solver#push_ctx;
                    let vars = List.map
                        (fun i -> (new var (sprintf "_a%d" i))) (range 0 n) in
                    List.iter (fun v -> solver#append (var_to_smt v)) vars;
                    List.iter2
                        (fun v (i, l, r) ->
                            solver#append_assert
                                (expr_to_smt (BinEx (GE, Var v, l)));
                            if not_nop r
                            then solver#append_assert
                                (expr_to_smt (BinEx (LT, Var v, r)));
                        ) vars comb;
                    let sum = List.fold_left
                        (fun e v ->
                            if is_nop e then Var v else BinEx (PLUS, Var v, e)
                        ) (Nop "") vars in
                    let sum_eq = BinEx (EQ, num_expr, sum) in
                    solver#append_assert (expr_to_smt sum_eq);
                    let exists_concrete = solver#check in
                    solver#pop_ctx;
                    exists_concrete
                ) combinations in
            let extr_num triples = List.map (fun (i, _, _) -> i) triples in
            List.map extr_num sat_triples_list
       end
;;

let identify_var_roles units =
    let roles = Hashtbl.create 10 in
    let fill_roles proc =
        let cfg = Cfg.mk_cfg (mir_to_lir proc#get_stmts) in
        let (int_roles: (int, (var, int_role) Hashtbl.t) Hashtbl.t) =
            visit_cfg (visit_basic_block transfer_roles)
                (join lub_int_role) (print_int_roles "roles") cfg in
        let body_sum =
            join_all_locs (join lub_int_role) (mk_bottom_val ()) int_roles in
        let skel = extract_skel proc#get_stmts in
        let fst_id =
            let is_norm s = (m_stmt_id s) <> -1 in
            (m_stmt_id (List.find is_norm skel.comp)) in
        let loc_roles =
            try Hashtbl.find int_roles fst_id
            with Not_found ->
                let m =
                    (sprintf "No analysis data for loc %d" fst_id) in
                raise (Failure m)
        in
        Hashtbl.iter
            (fun v r ->
                let is_const = match Hashtbl.find loc_roles v with
                    | IntervalInt (a, b) -> a = b   (* const *)
                    | _ -> false                    (* mutating *)
                in
                let new_role = if is_const
                then Scratch
                else match Hashtbl.find body_sum v with
                    | IntervalInt (a, b) -> BoundedInt (a, b)
                    | UnboundedInt -> LocalUnbounded
                    | Undefined ->
                        raise (Abstraction_error
                            (sprintf "Undefined type for %s" v#get_name))
                in
                Hashtbl.replace roles v new_role (* XXX: can we lose types? *)
            ) body_sum;
    in
    List.iter (function Proc proc -> fill_roles proc | _ -> ()) units;

    let replace_global = function
        | MDecl (_, v, e) -> (* global declaration *)
            if not v#is_symbolic
            then if LocalUnbounded <> (Hashtbl.find roles v)
            then raise (Abstraction_error
                    (sprintf "Shared variable %s is not unbounded" v#get_name))
            else Hashtbl.replace roles v SharedUnbounded
        | _ -> ()
    in
    List.iter (function | Stmt s -> replace_global s | _ -> ()) units;

    roles
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
    List.iter (fun c1 -> List.iter
        (fun c2 ->
            if c1 <> c2
            then begin
                solver#append_assert (sprintf "(not (< %s %s))"
                    (expr_to_smt c1) (expr_to_smt c2));
                if not solver#check
                then (Hashtbl.add cmp_tbl
                    ((Hashtbl.find id_map c1), (Hashtbl.find id_map c2)) true);
                solver#pop_ctx; solver#push_ctx
            end
        ) conds)
        conds;
    solver#pop_ctx;
    List.iter (fun c1 -> List.iter (fun c2 ->
        let i1 = (Hashtbl.find id_map c1) and i2 = (Hashtbl.find id_map c2) in
        if i1 <> i2
        then if not (Hashtbl.mem cmp_tbl (i1, i2))
            && not (Hashtbl.mem cmp_tbl (i2, i1))
        then raise (Abstraction_error (sprintf "No order for %s and %s"
            (expr_s c1) (expr_s c2))))
        conds) conds;

    List.sort
        (fun c1 c2 ->
            if c1 = c2
            then 0
            else
                let i1 = (Hashtbl.find id_map c1)
                    and i2 = (Hashtbl.find id_map c2) in
                if (Hashtbl.mem cmp_tbl (i1, i2))
                then -1
                else 1
        )
        conds
;;

let mk_context units =
    let ctx = new trans_context in
    ctx#set_var_roles (identify_var_roles units);
    log INFO " # Variable roles:";
    Hashtbl.iter
        (fun v r ->
            log INFO (sprintf "   %s -> %s" v#get_name (var_role_s r)))
        ctx#get_var_roles;
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
    let dom = new abs_domain sorted_conds in
    dom#print;
    dom
;;

(*
  Abstraction of an expression over a variable and symbolic parameters.
  is_leaf_fun evaluates an expression to true if no further expansion of
  expr must be performed.
 *)
let mk_expr_abstraction solver dom is_leaf_fun expr =
    (* replace the only leaf expression with a variable *)
    let mapping = Hashtbl.create 1 in
    let rec sub e =
        if (is_leaf_fun e)
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
    assert ((Hashtbl.length mapping) <= 1); (* handle only two arguments by now *)
    let res_var = new var "_res" in
    let expr_ren = sub expr in
    let vars_used = res_var :: (expr_used_vars expr_ren) (* i.e. _res; _arg0 *)
    in
    solver#push_ctx;
    (* introduce those variables to the SMT solver *)
    List.iter (fun v -> solver#append (var_to_smt v)) vars_used;
    (* find matching combinations *)
    let matching_vals =
        (dom#find_abs_vals ExistAbs solver
            (BinEx (EQ, Var (new var "_res"), expr_ren))) in
    solver#pop_ctx;
    let inv_map = hashtbl_inverse mapping in
    (* list of pairs of abstract values for ((_res, d'), (e(_arg0), d'')) *)
    let sub_var (v: var) : (token expr) =
        if Hashtbl.mem inv_map v then Hashtbl.find inv_map v else Var v in
    List.map
        (fun tuple ->
            List.map (fun (var, abs_val) -> (sub_var var, abs_val)) tuple
        ) matching_vals
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

let translate_expr ctx dom solver atype expr =
    let cmp_abs_var var_expr abs_val =
        if not (ctx#must_hack_expr var_expr)
        then BinEx (EQ, var_expr, Const abs_val)
        else (* hack: concretize the var_expriable back as a constraint *)
            dom#concretize var_expr abs_val
    in 
    let trans_rel_many_vars symb_expr =
        let matching_vals = (dom#find_abs_vals atype solver symb_expr) in
        (* create a disjunction of conjunctions enumerating abstract values:
            (vx == 0) && (vy == 1) || (vx == 2) && (vy == 0)            *)
        List.fold_left
            (fun conjuncts abs_tuple ->
                let conj = List.fold_left
                    (fun lits (var, abs_val) ->
                        let lit = cmp_abs_var (Var var) abs_val in
                        if not_nop lits then BinEx (AND, lits, lit) else lit
                    ) (Nop "") abs_tuple
                in
                if not_nop conjuncts then BinEx (OR, conjuncts, conj) else conj 
            ) (Nop "") matching_vals
    in
    let rec trans_e = function
        (* boolean combination of arithmetic constraints *)
        | BinEx (AND, lhs, rhs) ->
            BinEx (AND, (trans_e lhs), (trans_e rhs))
        | BinEx (OR, lhs, rhs) ->
            BinEx (OR, (trans_e lhs), (trans_e rhs))
        | UnEx  (NEG, lhs) ->
            UnEx (NEG, (trans_e lhs))
        (* comparison against a constant,
           comparison against a variable and a constant *)
        | BinEx (LT, lhs, rhs)
        | BinEx (LE, lhs, rhs)
        | BinEx (GT, lhs, rhs)
        | BinEx (GE, lhs, rhs)
        | BinEx (EQ, lhs, rhs)
        | BinEx (NE, lhs, rhs) as e ->
            if (expr_exists non_symbolic lhs)
            then if (expr_exists non_symbolic rhs)
                then trans_rel_many_vars e
                else BinEx ((op_of_expr e), lhs, (dom#map_concrete solver rhs))
            else BinEx ((op_of_expr e),
                (dom#map_concrete solver lhs), rhs)
        | _ -> raise (Abstraction_error
            (sprintf "No abstraction for: %s" (expr_s expr)))
    in
    trans_e expr
;;

(* The first phase of the abstraction takes place here *)
(* TODO: refactor it, should be simplified *)
let translate_stmt ctx dom solver stmt =
    let rec abs_stmt = function
    | MExpr (id, e) as s ->
        if not (expr_exists (over_dom ctx) e)
        then s
        else begin
        (* different kinds of expressions must be treated differently *)
            match e with
            | BinEx (ASGN, lhs, rhs) ->
                (* XXX: hack for shared variables in VASS *)
                if ctx#must_hack_expr lhs
                then s (* keep untouched *)
                else
                (* END of hack *)
                if (expr_exists non_symbolic rhs)
                then begin
                    if is_var rhs
                    (* foo = bar; keep untouched *)
                    then s
                    (* analyze all possible values of the right-hand side *)
                    else let expr_abs_vals =
                        mk_expr_abstraction solver dom
                            (fun e -> is_var e && not (has_expr_symbolic e)) rhs
                    in (mk_assign_unfolding lhs expr_abs_vals)
                end
                (* just substitute one abstract value on the right-hand side *)
                else MExpr (id, BinEx (ASGN, lhs, (dom#map_concrete solver rhs)))
            | _ -> MExpr (id, translate_expr ctx dom solver ExistAbs e)
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

    and
    abs_seq seq =
        List.fold_right (fun s l -> (abs_stmt s) :: l) seq []
    in
    abs_stmt stmt 
;;

let trans_prop_decl ctx dom solver decl_expr =
    let tr_e e =
        let used_vars = expr_used_vars e in
        let locals = List.filter (fun v -> v#proc_name <> "") used_vars in
        solver#push_ctx;
        List.iter solver#append (List.map var_to_smt locals);
        let abs_ex = translate_expr ctx dom solver UnivAbs e in
        solver#pop_ctx;
        abs_ex
    in
    let has_card = function
        | UnEx (CARD, _) -> true
        | _ -> false
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
            if not (expr_exists (over_dom ctx) e) || (expr_exists has_card e)
            then decl_expr
            else MDeclProp (id, v, PropGlob (tr_e e))
        | _ -> decl_expr
;;

let do_interval_abstraction ctx dom solver units = 
    let on_unit = function
        | Proc p ->
            solver#push_ctx;
            List.iter (fun v -> solver#append (var_to_smt v)) p#get_locals;
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

