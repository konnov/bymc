open Printf;;

open Parse;;
open Spin;;
open Spin_ir;;
open Spin_ir_imp;;
open Smt;;

exception Skeleton_not_supported of string;;
exception Abstraction_error of string;;

type var_role = Pc | Shared | Local | Next;;

let var_role_s r =
    match r with
    | Pc -> "pc"
    | Shared -> "shared"
    | Local -> "local"
    | Next -> "next"
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
            (* solver#set_debug true; *)
            List.iter solver#append smt_exprs;
            solver

        method get_globals = globals
        method set_globals g = globals <- g
        method get_var_roles = var_roles
        method set_var_roles r = var_roles <- r
        method get_assumps = assumps
        method set_assumps a = assumps <- a
    end
;;

class abs_domain conds_i =
    object(self)
        val mutable conds = conds_i             (* thresholds *)
        val mutable val_map = Hashtbl.create 10 (* from a cond to a value *)

        method print =
            printf " # Abstract domain: \n";
            Hashtbl.iter
                (fun c v -> printf "   %s -> %s\n" v (expr_s c)) val_map
        
        initializer
            List.iter
                (fun c -> Hashtbl.add val_map c
                    (sprintf "d%d" (Hashtbl.length val_map)))
                conds
    end
;;

let identify_var_roles units =
    let tbl = Hashtbl.create 10 in
    let assign_role is_local name =
        if not is_local
        then Shared
        else if name = "pc"
        then Pc
        else if "next_" = (String.sub name 0 (min 5 (String.length name)))
        then Next
        else Local
    in
    let process_stmt is_local s =
        match s with
            | Decl (v, e) ->
                if not v#is_symbolic
                then Hashtbl.add tbl v (assign_role is_local v#get_name)
            | _ -> ()
    in
    List.iter
        (fun u ->
            match u with
            | Stmt s -> process_stmt false s
            | Proc p -> List.iter (process_stmt true) p#get_stmts
            | _ -> ()
        )
        units;
    tbl
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
        if (r = Local || r = Next) && (is_expr_symbolic e)
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

let sort_thresholds ctx conds =
    let id_map = Hashtbl.create 10 in
    List.iter (fun c -> Hashtbl.add id_map c (Hashtbl.length id_map)) conds;
    let solver = ctx#run_solver in
    solver#push_ctx;
    let cmp_tbl = Hashtbl.create 10 in
    List.iter (fun c1 -> List.iter
        (fun c2 ->
            if c1 <> c2
            then begin
                solver#append (sprintf "(assert (not (< %s %s)))\n"
                    (expr_to_smt c1) (expr_to_smt c2));
                if not solver#check
                then (Hashtbl.add cmp_tbl
                    ((Hashtbl.find id_map c1), (Hashtbl.find id_map c2)) true);
                solver#pop_ctx; solver#push_ctx
            end
        ) conds)
        conds;
    close_out solver#get_cout;
    let _ = solver#stop in ();
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

let translate_seq assumps globals conds stmts =
    stmts
;;

let mk_context units =
    let ctx = new trans_context in
    ctx#set_var_roles (identify_var_roles units);
    print_endline " # Variable roles:";
    Hashtbl.iter
        (fun v r -> printf "   %s -> %s\n" v#get_name (var_role_s r))
        ctx#get_var_roles;
    ctx#set_assumps (extract_assumptions units);
    print_endline " # Assumptions:";
    List.iter (fun e -> printf "   assume(%s)\n" (expr_s e)) ctx#get_assumps;
    ctx#set_globals (extract_globals units);
    print_endline " # Globals:";
    List.iter (fun v -> printf "   var %s\n" v#get_name) ctx#get_globals;
    ctx
;;

let mk_domain units ctx =
    printf "> Inferring an abstract domain...\n";
    let all_stmts = List.fold_left
        (fun l u ->
            match u with
            | Proc p -> List.append l p#get_stmts
            | _ -> l
        )
        [] units
    in
    let conds = identify_conditions ctx#get_var_roles all_stmts in
    let sorted_conds = sort_thresholds ctx conds in
    new abs_domain(sorted_conds)
;;

let do_abstraction units =
    let ctx = mk_context units in
    let dom = mk_domain units ctx in
    dom#print
;;
