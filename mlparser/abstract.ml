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

let is_bounded_int = function
    | BoundedInt (_, _) -> true
    | _ -> false
;;

class ['tok] trans_context =
    object(self)
        val mutable globals: var list = []
        val mutable assumps: 'tok expr list = []
        val mutable var_roles: (var, var_role) Hashtbl.t = Hashtbl.create 1
        val mutable label_ctr = 10000 (* start with a high label *)

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
        method get_var_roles = var_roles
        method set_var_roles r = var_roles <- r
        method get_assumps = assumps
        method set_assumps a = assumps <- a

        method next_label_counter =
            let ctr = label_ctr in
            label_ctr <- label_ctr + 1;
            ctr
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
    end
;;

let identify_var_roles units =
    let roles = Hashtbl.create 10
    in
    let fill_roles proc =
        let cfg = Cfg.mk_cfg proc#get_stmts in
        let int_roles =
            visit_cfg (visit_basic_block transfer_roles)
                join_int_roles cfg (mk_bottom_val ()) in
        let body_sum = join_all_blocks join_int_roles
            (mk_bottom_val ()) int_roles in
        let regtbl = extract_skel cfg in
        let end_bbs = List.filter
            (fun bb -> RegEnd = (Hashtbl.find regtbl bb#get_lead_lab))
            (hashtbl_vals cfg)
        in
        Hashtbl.iter
            (fun v r ->
                let new_role =
                if List.for_all
                    (fun bb ->
                        let loc_roles = Hashtbl.find int_roles bb#get_lead_lab in
                        match Hashtbl.find loc_roles v with
                            | IntervalInt (a, b) -> a = b   (* const *)
                            | _ -> false                    (* mutating *)
                    ) end_bbs
                then Scratch
                else match Hashtbl.find body_sum v with
                    | IntervalInt (a, b) -> BoundedInt (a, b)
                    | UnboundedInt -> LocalUnbounded
                    | Undefined ->
                        raise (Abstraction_error
                            (sprintf "Undefined type for %s" v#get_name))
                in
                Hashtbl.replace roles v new_role (* XXX: can we lose types? *)
            )
            body_sum;
    in
    List.iter (function Proc proc -> fill_roles proc | _ -> ()) units;

    let replace_global = function
        | Decl (v, e) -> (* global declaration *)
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
        | (Expr e) :: tl -> List.append (on_expr e) (on_stmts tl)
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
    | (Stmt (Assume e)) :: tl -> e :: (extract_assumptions tl)
    | _ :: tl -> extract_assumptions tl
    | [] -> []
;;

let rec extract_globals units =
    match units with
    | Stmt Decl (v, _) :: tl -> v :: (extract_globals tl)
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
    let conds = identify_conditions ctx#get_var_roles all_stmts in
    let sorted_conds = sort_thresholds solver ctx conds in
    new abs_domain sorted_conds
;;

(* The first phase of the abstraction takes place here *)
let translate_stmt ctx dom solver s =
    let non_symbolic e =
        match e with
        | Var v -> not v#is_symbolic
        | _ -> false
    in
    let over_dom e =
        match e with
        | Var v ->
            v#is_symbolic || (is_bounded_int (ctx#get_role v))
        | _ -> false
    in
    let translate_assign lhs rhs =
        (* TODO: simplify for the case when rhs has only one variable *)
        let is_next_var name =
            let l = (String.length name) in
            if l > 3
            then "_nx" = (String.sub name (l - 3) 3)
            else false
        in
        let rec substitute_vars to_nx e =
            match e with
            | Var v -> 
                if to_nx
                then Var (new var (v#get_name ^ "_nx")) (* add _nx *)
                else if is_next_var v#get_name
                    then Var (new var (String.sub v#get_name 0
                        ((String.length v#get_name) - 3)))  (* remove _nx *)
                    else e
            | BinEx (tok, l, r) ->
                    BinEx (tok,
                        (substitute_vars to_nx l), (substitute_vars to_nx r))
            | UnEx (tok, l) -> UnEx (tok, (substitute_vars to_nx l))
            | _ -> e
        in
        (* add a suffix "_nx" to each variable in the left-hand side *)
        let lhs_ren = (substitute_vars true lhs) in
        let nx_used = expr_used_vars lhs_ren in
        solver#push_ctx;
        (* introduce those variables to the SMT solver *)
        List.iter (fun v -> solver#append (var_to_smt v)) nx_used;
        (* find matching combinations *)
        let matching_vals =
            (dom#find_abs_vals solver (BinEx (EQ, lhs_ren, rhs))) in
        solver#pop_ctx;
        (* create an if/fi enumerating all combinations of lhs and rhs *)
        let labs = List.map (fun _ -> ctx#next_label_counter) matching_vals in
        let exit_lab = ctx#next_label_counter in
        let guarded_actions =
            List.map2 (fun lab abs_tuple ->
                let guard = List.fold_left
                    (fun lits (var, abs_val) ->
                        if not (is_next_var var#get_name)
                        then let lit = BinEx (EQ, Var var, Const abs_val) in
                            if lits = Nop then lit else BinEx (AND, lits, lit)
                        else lits)
                    Nop abs_tuple
                in
                let assigns = List.fold_left
                    (fun seq (var, abs_val) ->
                        if (is_next_var var#get_name)
                        then let orig_var = (substitute_vars false (Var var)) in
                            Expr (BinEx (ASGN, orig_var, Const abs_val)) :: seq
                        else seq)
                    [] abs_tuple
                in
                List.concat [[Label lab; Expr guard;]; assigns; [Goto exit_lab]])
            labs matching_vals
        in
        If (labs, exit_lab)
        :: (List.append (List.concat guarded_actions) [(Label exit_lab)])
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
    match s with
    | Expr e ->
        if not (expr_exists over_dom e)
        then [s]
        else begin
        (* different kinds of expressions must be treated differently *)
            match e with
            | BinEx (ASGN, lhs, rhs) ->
                if (expr_exists non_symbolic rhs)
                then
                    if (match rhs with | Var _ -> true | _ -> false)
                    (* foo = bar; keep untouched *)
                    then [s]
                    (* analyze all possible values of the right-hand side *)
                    else (translate_assign lhs rhs)
                (* just substitute one abstract value on the right-hand side *)
                else [Expr (BinEx (ASGN, lhs, (dom#map_concrete solver rhs)))]
            | _ -> [Expr (translate_expr e)]
        end                
    | _ -> [s]
;;

let do_interval_abstraction ctx dom solver procs = 
    List.map
        (fun p ->
            solver#push_ctx;
            List.iter (fun v -> solver#append (var_to_smt v)) p#get_locals;
            let body = List.concat
                (List.map (translate_stmt ctx dom solver) p#get_stmts) in
            log DEBUG (sprintf " -> Abstract skel of proctype %s\n" p#get_name);
            List.iter (fun s -> log DEBUG (stmt_s s)) body;
            solver#pop_ctx;
            Proc (proc_replace_body p body)
        ) procs;
;;

let do_counter_abstraction ctx dom solver units = 
    let ctr_arr = new var "ktr" in
    ctr_arr#set_isarray true;
    ctr_arr#set_num_elems dom#length;
    Stmt (Decl (ctr_arr, Nop)) :: units
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
    let fo = open_out "abs_interval.prm" in
    List.iter (write_unit fo 0) (List.append other_units new_procs);
    close_out fo;
    (* end of debug output *)
    let new_units = do_counter_abstraction ctx dom solver
        (List.append other_units new_procs) in
    let _ = solver#stop in
    new_units
;;
