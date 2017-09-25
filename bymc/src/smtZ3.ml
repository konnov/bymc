(*
 An interface to Z3 using the new Z3 ML bindings (Z3 4.5.0)

 Igor Konnov, 2017
 *)
open Printf
open Str

open BatEnum
open Sexplib

(* this package requires Z3 OCaml bindings *)
open Z3

open Accums
open Debug
open PipeCmd
open SpinTypes
open Spin
open SpinIr
open SpinIrImp

open Smt

let var_to_fun_decl ctx var tp =
    let sym = Symbol.mk_string ctx var#mangled_name in
    let l, r = tp#range in
    let rng e = [ BinEx (GE, e, IntConst l); BinEx (LT, e, IntConst r) ] in
    let spin_var = Var var in
    let var_expr, constraints =
        match tp#basetype with
        | TBIT ->
            (Boolean.mk_const ctx sym, [])

        | TBYTE ->
            let bounds =
                if tp#has_range
                then rng spin_var
                else [ BinEx (AND,
                    BinEx (GE, spin_var, IntConst 0),
                    BinEx (LE, spin_var, IntConst 255))
                ]
            in
            (Arithmetic.Integer.mk_const ctx sym, bounds)

        | TSHORT  (* TODO: what is the range of short? *)
        | TINT ->
            let bounds =
                if tp#has_range
                then rng spin_var
                else []
            in
            (Arithmetic.Integer.mk_const ctx sym, bounds)

        | TUNSIGNED -> 
            let bounds =
                if tp#has_range
                then rng spin_var
                else [ BinEx (GE, spin_var, IntConst 0) ]
            in
            (Arithmetic.Integer.mk_const ctx sym, bounds)

        | TCHAN -> raise (Failure "Type chan is not supported")
        | TMTYPE -> raise (Failure "Type mtype is not supported")
        | TPROPOSITION -> raise (Failure "Type proposition is not supported")
        | TUNDEF -> raise (Failure "Undefined type met")
    in
    (assert (not tp#is_array)); (* arrays are not supported yet *)
    (var_expr, constraints)


(* TODO: just reusing Smt.expr_to_smt2, but could use virtually anything *)
let rec expr_to_key = function
    | Nop comment -> sprintf ";; %s\n" comment
    | IntConst i -> string_of_int i
    | Var v -> v#mangled_name

    | UnEx (tok, f) ->
        begin match tok with
        | UMIN -> sprintf "(- %s)" (expr_to_key f)
        | NEG  -> sprintf "(not %s)" (expr_to_key f)
        | _ ->
            raise (Failure
                (sprintf "No idea how to translate %s to SMT" (token_s tok)))
        end

    | BinEx (tok, l, r) ->
        begin match tok with
        | PLUS  -> sprintf "(+ %s %s)" (expr_to_key l) (expr_to_key r)
        | MINUS -> sprintf "(- %s %s)" (expr_to_key l) (expr_to_key r)
        | MULT  -> sprintf "(* %s %s)" (expr_to_key l) (expr_to_key r)
        | DIV   -> sprintf "(div %s %s)" (expr_to_key l) (expr_to_key r)
        | MOD   -> sprintf "(mod %s %s)" (expr_to_key l) (expr_to_key r)
        | GT    -> sprintf "(> %s %s)" (expr_to_key l) (expr_to_key r)
        | LT    -> sprintf "(< %s %s)" (expr_to_key l) (expr_to_key r)
        | GE    -> sprintf "(>= %s %s)"  (expr_to_key l) (expr_to_key r)
        | LE    -> sprintf "(<= %s %s)"  (expr_to_key l) (expr_to_key r)
        | EQ    -> sprintf "(= %s %s)"  (expr_to_key l) (expr_to_key r)
        | NE    -> sprintf "(not (= %s %s))"  (expr_to_key l) (expr_to_key r)
        | AND   -> sprintf "(and %s %s)" (expr_to_key l) (expr_to_key r)
        | OR    -> sprintf "(or %s %s)"  (expr_to_key l) (expr_to_key r)
        | EQUIV -> sprintf "(= %s %s)"  (expr_to_key l) (expr_to_key r)
        | IMPLIES -> sprintf "(=> %s %s)"  (expr_to_key l) (expr_to_key r)
        | ARR_ACCESS -> sprintf "(select %s %s)" (expr_to_key l) (expr_to_key r)
        | _ -> raise (Failure
                (sprintf "No idea how to translate '%s' to SMT" (token_s tok)))
        end

    | Phi (lhs, rhs) ->
            raise (Failure "Phi to SMT is not supported")

    | LabelRef (proc_name, lab_name) ->
            raise (Failure "LabelRef to SMT is not supported")


let expr_to_z3 ctx vars ex =
    let rec trans = function
    | Nop comment -> raise (Failure (sprintf "Not supported: Nop '%s'" comment))
    | IntConst i -> Arithmetic.Integer.mk_numeral_i ctx i
    | Var v -> Hashtbl.find vars v#mangled_name

    | UnEx (tok, f) ->
        begin match tok with
        | UMIN -> Arithmetic.mk_unary_minus ctx (trans f)
        | NEG  -> Boolean.mk_not ctx (trans f)
        | _ ->
            raise (Failure
                (sprintf "No idea how to translate %s to SMT" (token_s tok)))
        end

    | BinEx (tok, l, r) ->
        begin match tok with
        | PLUS  -> Arithmetic.mk_add ctx [trans l; trans r]
        | MINUS -> Arithmetic.mk_sub ctx [trans l; trans r]
        | MULT  -> Arithmetic.mk_mul ctx [trans l; trans r]
        | DIV   -> Arithmetic.mk_div ctx (trans l) (trans r)
        | MOD   -> Arithmetic.Integer.mk_mod ctx (trans l) (trans r)
        | GT    -> Arithmetic.mk_gt ctx (trans l) (trans r)
        | LT    -> Arithmetic.mk_lt ctx (trans l) (trans r)
        | GE    -> Arithmetic.mk_ge ctx (trans l) (trans r)
        | LE    -> Arithmetic.mk_le ctx (trans l) (trans r)
        | EQ    -> Boolean.mk_eq ctx (trans l) (trans r)
        | NE    -> Boolean.mk_not ctx (Boolean.mk_eq ctx (trans l) (trans r))
        | AND   -> Boolean.mk_and ctx [trans l; trans r]
        | OR    -> Boolean.mk_or ctx [trans l; trans r]
        | EQUIV -> Boolean.mk_iff ctx (trans l) (trans r)
        | IMPLIES -> Boolean.mk_implies ctx (trans l) (trans r)
        | _ -> raise (Failure
                (sprintf "No idea how to translate '%s' to SMT" (token_s tok)))
        end

    | Phi (lhs, rhs) ->
            raise (Failure "Phi to SMT is not supported")

    | LabelRef (proc_name, lab_name) ->
            raise (Failure "LabelRef to SMT is not supported")
    in
    trans ex

(**
  An SMT solver implementation that uses Z3 bindings.
*)
class z3_smt name =
    object(self)
        inherit smt_solver

        val mutable m_context: Z3.context = mk_context []
        val mutable m_solver: Z3.Solver.solver option = None
        val mutable m_vars: (string, Z3.Expr.expr) Hashtbl.t
            = Hashtbl.create 10

        val mutable debug = false
        val mutable m_enable_log = false
        val mutable m_need_evidence = false
        val mutable m_need_unsat_cores = false
        val mutable m_incremental = true
        val mutable collect_asserts = false
        (** the number of stack pushes executed within consistent context *)
        val mutable m_pushes = 0
        (** the number of stack pushes executed within inconsistent context *)
        val mutable m_inconsistent_pushes = 0
        (** the last id used in the assertions *)
        val mutable m_last_id = 1
        (** the number of times the solver has been started *)
        val mutable m_nstarts = 0
        (** the theory to use *)
        val mutable m_logic = None

        method start =
            let bool_s = string_of_bool in
            let cfg = [
                ("model", bool_s m_need_evidence);
                ("unsat_core", bool_s m_need_unsat_cores)
            ]
            in
            m_context <- mk_context cfg;
            m_solver <- Some (Z3.Solver.mk_simple_solver m_context);
            if m_incremental
            then self#push_ctx; (* a backup context to reset *)
            m_nstarts <- m_nstarts + 1

        
        method stop =
            self#reset; (* hopefully, we clean all data structures *)
            m_solver <- None

        method reset =
            Z3.Solver.reset (get_some m_solver);
            Hashtbl.clear m_vars;
            m_need_evidence <- false;
            collect_asserts <- false;
            m_pushes <- 0;
            m_inconsistent_pushes <- 0;
            if m_incremental
            then self#push_ctx

        method clone_not_started ?logic new_name =
            let copy = new z3_smt new_name in
            if logic <> None
            then copy#set_logic (get_some logic);
            copy#set_incremental_mode m_incremental;
            copy#set_need_model m_need_evidence;
            copy#set_need_unsat_cores m_need_unsat_cores;
            copy#set_collect_asserts collect_asserts;
            copy#set_enable_log m_enable_log;
            copy#set_debug debug;
            (copy :> smt_solver)

        method set_logic (theory: string): unit =
            m_logic <- Some theory (* pick a tactic? *)

        method append_var_def (v: var) (tp: data_type) =
            let (var_expr, constr) = var_to_fun_decl m_context v tp in
            Hashtbl.replace m_vars v#mangled_name var_expr;
            Solver.add (get_some m_solver)
                (List.map (expr_to_z3 m_context m_vars) constr)

        method comment (line: string) =
            ()  (* ignore for the moment *)

        method append_expr expr =
            if SpinIr.not_nop expr
            then Solver.add (get_some m_solver) [expr_to_z3 m_context m_vars expr];
            -1 (* TODO: add expression ids *)

        method push_ctx =
            m_incremental <- true;
            m_pushes <- m_pushes + 1;
            Z3.Solver.push (get_some m_solver)

        (** Get the current stack level (nr. of pushes). Use for debugging *)
        method get_stack_level =
            m_pushes + m_inconsistent_pushes

        method pop_ctx =
            m_pushes <- m_pushes - 1;
            Z3.Solver.pop (get_some m_solver) 1

        method private pop_n n =
            m_pushes <- m_pushes - n;
            Z3.Solver.pop (get_some m_solver) n

        method check =
            let status = Z3.Solver.check (get_some m_solver) [] in
            if status = Z3.Solver.UNKNOWN
            then raise (Failure "Z3 returned UNKNOWN");
            status = Z3.Solver.SATISFIABLE

        method set_need_model b =
            (* set before start *)
            m_need_evidence <- b

        method get_need_model = m_need_evidence

        method set_need_unsat_cores b =
            (* set before start *)
            m_need_unsat_cores <- b

        method get_need_unsat_cores = m_need_unsat_cores
            
        method get_model_query = Q.new_query expr_to_key

        method submit_query (query: Q.query_t) =
            let keys = Smt.Q.keys query in
            let new_q = Q.new_query expr_to_key in
            let to_int str =
                try int_of_string str
                with Failure m ->
                    printf "Cannot convert %s to int\n" str;
                    raise (Failure m)
            in
            let umin_re = Str.regexp "(- \\([-0-9]+\\))" in
            let each_key model key =
                let var_expr =
                    try Hashtbl.find m_vars key
                    with Not_found ->
                        raise (Failure ("No variable " ^ key ^ " in SMT query"))
                in
                match Model.eval model var_expr true with
                | None ->
                    raise (Failure (sprintf "No model for %s" key))

                | Some z3ex ->
                    let str = Expr.to_string z3ex in
                    let int_val =
                        if Str.string_match umin_re str 0
                        then -(int_of_string (Str.matched_group 1 str))
                        else to_int str
                    in
                    ignore (Smt.Q.add_result query new_q key (IntConst int_val))
            in
            begin
                match Solver.get_model (get_some m_solver) with
                | None ->
                    raise (Failure "No model")

                | Some model ->
                    List.iter (each_key model) keys
            end;
            new_q

        method get_collect_asserts = collect_asserts

        method set_collect_asserts b = collect_asserts <- b

        method get_unsat_cores =
            (* collect unsatisfiable cores *)
            raise (Failure "unsat_cores not supported yet")

        method set_debug flag = debug <- flag

        method set_enable_lockstep b = ()

        method get_enable_lockstep = false

        method set_enable_log b = m_enable_log <- b

        method get_enable_log = m_enable_log

        method set_incremental_mode b =
            m_incremental <- b


        method get_incremental_mode = m_incremental
    end


