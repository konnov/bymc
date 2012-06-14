open Printf;;

open Cfg;;
open Spin;;
open Spin_ir;;
open Spin_ir_imp;;
open Smt;;
open Analysis;;
open Skel_struc;;
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

let is_local_unbounded = function
    | LocalUnbounded -> true
    | _ -> false
;;

class ['tok] trans_context =
    object(self)
        val mutable globals: var list = []
        val mutable assumps: 'tok expr list = []
        val mutable var_roles: (var, var_role) Hashtbl.t = Hashtbl.create 1

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

        method find_pc =
            let is_pc role =
                match role with
                | BoundedInt (_, _) -> true
                | _ -> false
            in
            let pcs =
                (Hashtbl.fold
                    (fun v r lst -> if is_pc r then v :: lst else lst)
                    var_roles []) in
            match pcs with
            | [v] -> v
            | [] -> raise (Abstraction_error "No variable like pc is found.")
            | _ :: (_ :: _) -> 
                 raise (Abstraction_error
                        "More than one bounded variable. Which is pc?")

        method get_role v = Hashtbl.find var_roles v

        method get_globals = globals
        method set_globals g = globals <- g
        method get_var_roles = var_roles
        method set_var_roles r = var_roles <- r
        method get_assumps = assumps
        method set_assumps a = assumps <- a
    end
;;

exception Found of int;;

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
                    (List.combine conds (List.append (List.tl conds) [Nop]))
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
                        if r <> Nop
                        then solver#append_assert
                            (expr_to_smt (BinEx (LT, symb_expr, r)));
                        if solver#check
                        then begin
                            solver#pop_ctx;
                            raise (Found (Hashtbl.find val_map l))
                        end;
                        solver#pop_ctx
                    )
                    cond_intervals;
                raise (Abstraction_error
                    (sprintf "No abstract value for %s" (expr_s symb_expr)))
            with Found i ->
                (Const i: Spin.token expr)

        method find_abs_vals (solver: yices_smt) (symb_expr: 't expr)
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
                (* TODO: refactor, it is so complicated! *)
                solver#push_ctx;
                let matching_tuples = List.fold_left
                    (fun lst triples (* of (abs_val, lcond, rcond) *) ->
                        solver#push_ctx;
                        List.iter2
                            (fun var (i, l, r) ->
                                solver#append_assert
                                    (expr_to_smt (BinEx (GE, Var var, l)));
                                if r <> Nop
                                then solver#append_assert
                                    (expr_to_smt (BinEx (LT, Var var, r)));
                            ) used triples;
                        solver#append_assert (expr_to_smt symb_expr);
                        let exists_concrete = solver#check in
                        solver#pop_ctx;
                        if exists_concrete
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
            if n > 4
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
                            if r <> Nop
                            then solver#append_assert
                                (expr_to_smt (BinEx (LT, Var v, r)));
                        ) vars comb;
                    let sum = List.fold_left
                        (fun e v ->
                            if e = Nop then Var v else BinEx (PLUS, Var v, e)
                        ) Nop vars in
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
                join_int_roles cfg (mk_bottom_val ()) in
        let body_sum =
            join_all_locs join_int_roles (mk_bottom_val ()) int_roles in
        let skel = extract_skel proc#get_stmts in
        Hashtbl.iter
            (fun v r ->
                let loc_roles = Hashtbl.find int_roles (m_stmt_id skel.guard) in
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
let rec is_expr_symbolic e =
    match e with
    | Const _ -> true
    | Var v -> v#is_symbolic
    | UnEx (op, se) -> op = UMIN && is_expr_symbolic se
    | BinEx (op, le, re) ->
        (List.mem op [PLUS; MINUS; MULT; DIV; MOD])
            && (is_expr_symbolic le) && (is_expr_symbolic re)
    | _ -> false
;;

let identify_conditions var_roles stmts =
    let on_cond v e =
        let r = Hashtbl.find var_roles v in
        if (r = LocalUnbounded || r = Scratch) && (is_expr_symbolic e)
        then [e]
        else []
    in
    let rec on_expr e =
        match e with
        | BinEx(AND, l, r) -> List.append (on_expr l) (on_expr r)
        | BinEx(OR, l, r)  -> List.append (on_expr l) (on_expr r)
        | UnEx(NEG, l)     -> on_expr l
        | BinEx(LT, Var v, e) -> on_cond v e
        | BinEx(GE, Var v, e) -> on_cond v e
        | BinEx(LE, e, Var v) -> on_cond v e
        | BinEx(GT, e, Var v) -> on_cond v e
        | BinEx(LE, Var v, e) ->
            raise (Skeleton_not_supported "var <= expr")
        | BinEx(GE, e, Var v) ->
            raise (Skeleton_not_supported "expr >= var")
        | BinEx(GT, Var v, e) ->
            raise (Skeleton_not_supported "var > expr")
        | BinEx(LT, e, Var v) ->
            raise (Skeleton_not_supported "expr < var")
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

let mk_domain solver ctx procs =
    log INFO "> Extracting an abstract domain...";
   
    let all_stmts = List.concat (List.map (fun p -> p#get_stmts) procs) in
    let conds = identify_conditions ctx#get_var_roles (mir_to_lir all_stmts) in
    let sorted_conds = sort_thresholds solver ctx conds in
    new abs_domain sorted_conds
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
        (dom#find_abs_vals solver
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
                    if not (is_out_var ex) (* XXX: magic name! *)
                    then let lit = BinEx (EQ, ex, Const abs_val) in
                        if lits = Nop then lit else BinEx (AND, lits, lit)
                    else lits (* skip this var *))
                Nop abs_tuple
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

(* The first phase of the abstraction takes place here *)
(* TODO: refactor it, should be simplified *)
let translate_stmt ctx dom solver stmt =
    let non_symbolic = function
        | Var v -> not v#is_symbolic
        | _ -> false
    in
    let over_dom = function
        | Var v ->
            begin
                try
                    v#is_symbolic || (is_unbounded (ctx#get_role v))
                with Not_found ->
                    raise (Abstraction_error
                        (sprintf "No role for %s" v#get_name))
            end
        | _ -> false
    in
    let trans_rel_many_vars symb_expr =
        let matching_vals = (dom#find_abs_vals solver symb_expr) in
        (* create a disjunction of conjunctions enumerating abstract values:
            (vx == 0) && (vy == 1) || (vx == 2) && (vy == 0)            *)
        List.fold_left
            (fun conjuncts abs_tuple ->
                let conj = List.fold_left
                    (fun lits (var, abs_val) ->
                        let lit = BinEx (EQ, Var var, Const abs_val) in
                        if lits = Nop
                        then lit
                        else BinEx (AND, lits, lit))
                    Nop abs_tuple
                in
                if conjuncts = Nop
                then conj
                else BinEx (OR, conjuncts, conj))
            Nop matching_vals
    in
    let rec translate_expr e =
        match e with
            (* boolean combination of arithmetic constraints *)
            | BinEx (AND, lhs, rhs) ->
                BinEx (AND, (translate_expr lhs), (translate_expr rhs))
            | BinEx (OR, lhs, rhs) ->
                BinEx (OR, (translate_expr lhs), (translate_expr rhs))
            | UnEx  (NEG, lhs) ->
                UnEx (NEG, (translate_expr lhs))
            (* comparison against a constant,
               comparison against a variable and a constant *)
            | BinEx (LT, lhs, rhs)
            | BinEx (LE, lhs, rhs)
            | BinEx (GT, lhs, rhs)
            | BinEx (GE, lhs, rhs)
            | BinEx (EQ, lhs, rhs)
            | BinEx (NE, lhs, rhs) ->
                if (expr_exists non_symbolic lhs)
                then if (expr_exists non_symbolic rhs)
                    then trans_rel_many_vars e
                    else BinEx ((op_of_expr e), lhs, (dom#map_concrete solver rhs))
                else BinEx ((op_of_expr e),
                    (dom#map_concrete solver lhs), rhs)
            | _ -> raise (Abstraction_error
                (sprintf "No abstraction for: %s" (expr_s e)))
    in
    let rec abs_stmt = function
    | MExpr (id, e) as s ->
        if not (expr_exists over_dom e)
        then s
        else begin
        (* different kinds of expressions must be treated differently *)
            match e with
            | BinEx (ASGN, lhs, rhs) ->
                if (expr_exists non_symbolic rhs)
                then
                    if (match rhs with | Var _ -> true | _ -> false)
                    (* foo = bar; keep untouched *)
                    then s
                    (* analyze all possible values of the right-hand side *)
                    else let expr_abs_vals =
                        mk_expr_abstraction solver dom
                            (fun e -> is_var e && not (is_expr_symbolic e)) rhs
                    in (mk_assign_unfolding lhs expr_abs_vals)
                (* just substitute one abstract value on the right-hand side *)
                else MExpr (id, BinEx (ASGN, lhs, (dom#map_concrete solver rhs)))
            | _ -> MExpr (id, translate_expr e)
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

let do_interval_abstraction ctx dom solver procs = 
    List.map
        (fun p ->
            solver#push_ctx;
            List.iter (fun v -> solver#append (var_to_smt v)) p#get_locals;
            let body = List.map (translate_stmt ctx dom solver) p#get_stmts in
            log DEBUG (sprintf " -> Abstract skel of proctype %s\n" p#get_name);
            List.iter (fun s -> log DEBUG (mir_stmt_s s)) body;
            solver#pop_ctx;
            Proc (proc_replace_body p body)
        ) procs;
;;

class ctr_abs_ctx dom t_ctx =
    object
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

let do_counter_abstraction t_ctx dom solver units =
    let ctr_ctx = new ctr_abs_ctx dom t_ctx in
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
    let replace_init guard active_expr decls init_stmts =
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
        [mk_nondet_choice option_list]
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
            let ktr_i = BinEx (ARRAY_DEREF, Var ctr_ctx#get_ctr, idx_ex) in
            let expr_abs_vals =
                mk_expr_abstraction solver dom
                    (function | BinEx (ARRAY_DEREF, _, _) -> true | _ -> false)
                    (BinEx (tok, ktr_i, Const 1)) in
            [mk_assign_unfolding ktr_i expr_abs_vals]
        in
        (mk_ctr_ex prev_idx_ex MINUS)
            @ (mk_ctr_ex next_idx_ex PLUS)
            @ new_update
    in
    let abstract_proc p =
        let body = remove_bad_statements p#get_stmts in
        let skel = extract_skel body in
        let main_lab = mk_uniq_label () in
        let new_init =
            replace_init skel.guard p#get_active_expr skel.decl skel.init
        in
        let new_update = replace_update skel.update body in
        let new_comp_upd = MAtomic (-1, skel.comp @ new_update) in
        let new_body = 
            skel.decl @ new_init @ [MLabel (-1, main_lab)]
            @ counter_guard @
            [MIf (-1, [MOptGuarded ([skel.guard; new_comp_upd]); MOptElse []]);
             MGoto (-1, main_lab)]
        in
        let new_proc = proc_replace_body p new_body in
        new_proc#set_active_expr (Const 1);
        new_proc
    in
    let new_units =
        List.map (function Proc p -> Proc (abstract_proc p) | _ as u -> u)
        units in
    (Stmt (MDecl (-1, ctr_ctx#get_ctr, Nop))) :: new_units
;;

let do_abstraction units =
    let procs, other_units = List.fold_left
        (fun (lp, lo) u -> match u with
            | Proc p -> (p :: lp, lo)
            | _ -> (lp, u :: lo)
        ) ([], []) units
    in
    let ctx = mk_context units in
    let solver = ctx#run_solver in
    let dom = mk_domain solver ctx procs in
    if may_log INFO then dom#print;
    let new_procs = do_interval_abstraction ctx dom solver procs in
    (* debug output *)
    let fo = open_out "abs-interval.prm" in
    List.iter (write_unit fo 0) (List.append other_units new_procs);
    close_out fo;
    (* end of debug output *)
    let new_units = do_counter_abstraction ctx dom solver
        (List.append other_units new_procs) in
    let _ = solver#stop in
    new_units
;;
