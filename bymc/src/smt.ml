(* utility functions to integrate with Yices *)

open Printf
open Str

open Debug
open PipeCmd
open SpinTypes
open Spin
open SpinIr
open SpinIrImp

exception Smt_error of string


module Q = struct
    type query_result_t =
        | Cached    (** the query is cached, once 'submit' is invoked,
                         the result will be available for the same query *)
        | NoResult   (** nothing is associated with the query *)
        | Result of (Spin.token SpinIr.expr)
                     (** the result of a previously cached query *)

    type query_t = {
        expr_to_smt_f: token expr -> string;
        frozen: bool;
        tab: (string, query_result_t) Hashtbl.t
    }

    let query_result_s q = function
        | Cached -> "Cached"
        | NoResult -> "NoResult"
        | Result e -> "Result " ^ (q.expr_to_smt_f e)

    let new_query expr_to_smt_f = 
        { frozen = false; expr_to_smt_f; tab = Hashtbl.create 10 }

    let try_get (q: query_t) (key: token expr) =
        let e_s = q.expr_to_smt_f key in
        try Hashtbl.find q.tab e_s
        with Not_found ->
            if q.frozen
            then NoResult
            else begin
                Hashtbl.add q.tab e_s Cached;
                Cached
            end

    let add_result (q: query_t) (nq: query_t) (key: string) (value: token expr) =
        try begin
            let _ = Hashtbl.find q.tab key in
            Hashtbl.add nq.tab key (Result value);
            nq
        end with Not_found ->
            nq

    let print_contents (q: query_t) =
        let p s r = printf "   %s <- %s\n" s (query_result_s q r) in
        printf "\n ***** query contents *****\n";
        Hashtbl.iter p q.tab
                
end


class virtual smt_solver =
    object
        (** fork a new process that executes 'yices' *)
        method virtual start: unit

        (** stop the solver process *)
        method virtual stop: unit

        (** reset the solver *)
        method virtual reset: unit

        (** add a comment (free of side effects) *)
        method virtual comment: string -> unit

        (** declare a variable *)
        method virtual append_var_def: SpinIr.var -> SpinIr.data_type -> unit

        (** Add an expression.
            @return an assertion id, if set_collect_asserts was called with true
         *)
        method virtual append_expr: Spin.token SpinIr.expr -> int

        (** push the context *)
        method virtual push_ctx: unit

        (** pop the context *)
        method virtual pop_ctx: unit

        (** get the number of pushes minus number of pops made so far *)
        method virtual get_stack_level: int

        (** check, whether the current context is satisfiable.
            @return true if sat
         *)
        method virtual check: bool

        (** ask the solver to provide a model of sat *)
        method virtual set_need_model: bool -> unit

        (** check, whether the solver is going to construct a sat model *)
        method virtual get_need_model: bool

        method virtual get_model_query: Q.query_t

        method virtual submit_query: Q.query_t -> Q.query_t

        (** track the assertions, in order to collect unsat cores *)
        method virtual set_collect_asserts: bool -> unit

        (** are the assertions collected *)
        method virtual get_collect_asserts: bool

        (** get an unsat core, which is the list of assertion ids
            that were provided by the solver with append_expr *)
        method virtual get_unsat_cores: int list

        (** indicate, whether debug information is needed *)
        method virtual set_debug: bool -> unit
    end


let rec expr_to_smt e =
    match e with
    | Nop comment -> sprintf ";; %s\n" comment
    | Const i -> string_of_int i
    | Var v -> v#mangled_name
    | UnEx (tok, f) ->
        begin match tok with
        | UMIN -> sprintf "(- %s)" (expr_to_smt f)
        | NEG  -> sprintf "(not %s)" (expr_to_smt f)
        | _ ->
            raise (Failure
                (sprintf "No idea how to translate %s to SMT" (token_s tok)))
        end
    | BinEx (tok, l, r) ->
        begin match tok with
        | PLUS  -> sprintf "(+ %s %s)" (expr_to_smt l) (expr_to_smt r)
        | MINUS -> sprintf "(- %s %s)" (expr_to_smt l) (expr_to_smt r)
        | MULT  -> sprintf "(* %s %s)" (expr_to_smt l) (expr_to_smt r)
        | DIV   -> sprintf "(div %s %s)" (expr_to_smt l) (expr_to_smt r)
        | MOD   -> sprintf "(mod %s %s)" (expr_to_smt l) (expr_to_smt r)
        | GT    -> sprintf "(> %s %s)" (expr_to_smt l) (expr_to_smt r)
        | LT    -> sprintf "(< %s %s)" (expr_to_smt l) (expr_to_smt r)
        | GE    -> sprintf "(>= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | LE    -> sprintf "(<= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | EQ    -> sprintf "(= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | NE    -> sprintf "(/= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | AND   -> sprintf "(and %s %s)" (expr_to_smt l) (expr_to_smt r)
        | OR    -> sprintf "(or %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | EQUIV -> sprintf "(= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | IMPLIES -> sprintf "(=> %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | ARR_ACCESS -> sprintf "(%s %s)" (expr_to_smt l) (expr_to_smt r)
        | _ -> raise (Failure
                (sprintf "No idea how to translate '%s' to SMT" (token_s tok)))
        end

    | Phi (lhs, rhs) ->
            raise (Failure "Phi to SMT is not supported")

    | LabelRef (proc_name, lab_name) ->
            raise (Failure "LabelRef to SMT is not supported")


let var_to_smt var tp =
    let base_type = match tp#basetype with
    | TBIT -> "bool"
    | TBYTE -> "int"
    | TSHORT -> "int"
    | TINT -> "int"
    | TUNSIGNED -> "nat"
    | TCHAN -> raise (Failure "Type chan is not supported")
    | TMTYPE -> raise (Failure "Type mtype is not supported")
    | TPROPOSITION -> raise (Failure "Type proposition is not supported")
    | TUNDEF -> raise (Failure "Undefined type met")
    in
    let complex_type =
        let subtype =
            if tp#has_range
            then let l, r = tp#range in
                sprintf "(subrange %d %d)" l (r - 1)
            else base_type
        in
        if tp#is_array
        then sprintf "(-> (subrange 0 %d) %s)" (tp#nelems - 1) subtype
        else subtype
    in
    sprintf "(define %s :: %s)" var#mangled_name complex_type


let parse_smt_model_q query lines =
    let var_re = Str.regexp "(= \\([_a-zA-Z0-9]+\\) \\([-0-9]+\\))" in
    let arr_re =
        Str.regexp "(= (\\([_a-zA-Z][_a-zA-Z0-9]*\\) \\([0-9]+\\)) \\([-0-9]+\\))"
    in
    let alias_re =
        Str.regexp ("(= \\([_a-zA-Z][_a-zA-Z0-9]*\\) \\([_a-zA-Z][_a-zA-Z0-9]*\\))")
    in
    let aliases = Hashtbl.create 5 in
    let add_alias origin alias = Hashtbl.add aliases origin alias in
    let get_aliases origin = Hashtbl.find_all aliases origin in

    let parse_line newq line =
        if Str.string_match var_re line 0
        then begin
            (* e.g., (= x 1) *)
            let variable = Str.matched_group 1 line in
            (* we support ints only, don't we? *)
            let value = int_of_string (Str.matched_group 2 line) in
            Q.add_result query newq variable (Const value)
        end
        else if Str.string_match arr_re line 0
        then begin
            (* e.g., (= (x 11) 0) *)
            let name = Str.matched_group 1 line in
            let index = int_of_string (Str.matched_group 2 line) in
            let value = int_of_string (Str.matched_group 3 line) in

            let mk_access n i = sprintf "(%s %d)" n i in
            let each_alias q alias =
                Q.add_result query q (mk_access alias index) (Const value)
            in
            (* the expression *)
            List.fold_left each_alias newq (name :: (get_aliases name)) 
        end else if Str.string_match alias_re line 0
        then begin
            (* (= alias origin) *)
            let alias = Str.matched_group 1 line in
            let origin = Str.matched_group 2 line in
            add_alias origin alias;
            newq
        end else newq
    in
    let new_query = List.fold_left parse_line (Q.new_query expr_to_smt) lines in
    { new_query with Q.frozen = true }


(* The interface to the SMT solver (yices).
   We are using the text interface, as it is way easier to debug. *)
class yices_smt (solver_name: string) =
    object(self)
        inherit smt_solver

        (* for how long we wait for output from yices if check is issued *)
        val check_timeout_sec = 3600.0
        (* for how long we wait for output from yices if another command is issued*)
        val timeout_sec = 10.0
        val mutable pid = 0
        val mutable clog = stdout
        val mutable m_pipe_cmd = PipeCmd.null ()
        val mutable debug = false
        val mutable m_need_evidence = false
        val mutable collect_asserts = false
        val mutable poll_tm_sec = 10.0
        (** the number of stack pushes executed within consistent context *)
        val mutable m_pushes = 0
        (** the number of stack pushes executed within inconsistent context *)
        val mutable m_inconsistent_pushes = 0

        method start =
            assert(PipeCmd.is_null m_pipe_cmd);
            m_pipe_cmd <- PipeCmd.create solver_name [||] (solver_name ^ ".err");
            clog <- open_out (solver_name ^ ".log");
            ignore (self#check);
            self#append "(set-verbosity! 2)\n" (* to track assert+ *)
        
        method stop =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            close_out clog;
            ignore (PipeCmd.destroy m_pipe_cmd);
            m_pipe_cmd <- PipeCmd.null ()

        method reset =
            self#append "(reset)";
            self#sync;
            m_need_evidence <- false;
            collect_asserts <- false;
            m_pushes <- 0;
            m_inconsistent_pushes <- 0

        method append_var_def (v: var) (tp: data_type) =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            self#append (var_to_smt v tp)

        method comment (line: string) =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            self#append (";; " ^ line)

        method append_expr expr =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            let eid = ref 0 in
            let e_s = expr_to_smt expr in
            let is_comment = (String.length e_s) > 1
                    && e_s.[0] = ';' && e_s.[1] = ';' in
            if not is_comment
            then begin 
                if not collect_asserts
                then self#append (sprintf "(assert %s)" e_s)
                else begin
                    (* XXX: may block if the verbosity level < 2 *)
                    self#sync;
                    self#append (sprintf "(assert+ %s)" e_s);
                    let line = self#read_line in
                    if (Str.string_match (Str.regexp "id: \\([0-9]+\\)") line 0)
                    then
                        let id = int_of_string (Str.matched_group 1 line) in
                        eid := id
                end;
                !eid
            end else -1

        method push_ctx =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            self#sync;
            self#append "(status)"; (* it can be unsat already *)
            if not (self#is_out_sat true)
            then begin
                self#comment "push in inconsistent context. Ignored.";
                m_inconsistent_pushes <- m_inconsistent_pushes + 1
            end else begin
                m_pushes <- m_pushes + 1;
                self#append "(push)"
            end

        (** Get the current stack level (nr. of pushes). Use for debugging *)
        method get_stack_level =
            m_pushes + m_inconsistent_pushes

        method pop_ctx =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            if m_pushes + m_inconsistent_pushes = 0
            then raise (Failure ("pop: yices stack is empty!"));
            if m_inconsistent_pushes > 0
            then begin
                self#comment "pop from inconsistent context.";
                m_inconsistent_pushes <- m_inconsistent_pushes - 1
            end else begin
                m_pushes <- m_pushes - 1;
                self#append "(pop)"
            end


        method check =
            self#sync;
            self#append "(status)"; (* it can be unsat already *)
            if not (self#is_out_sat true)
            then false
            else begin
                self#sync;
                self#append "(check)";
                let res = self#is_out_sat false in
                res
            end

        method set_need_model b =
            m_need_evidence <- b;
            if b
            then self#append "(set-evidence! true)"
            else self#append "(set-evidence! false)"

        method get_need_model = m_need_evidence
            
        method get_model_query = Q.new_query expr_to_smt

        method submit_query (query: Q.query_t) =
            (* same as sync but the lines are collected *)
            let lines = ref [] in
            self#append "(echo \"EOEV\\n\")";
            let stop = ref false in
            while not !stop do
                let line = self#read_line in
                if "EOEV" = line
                then stop := true
                else lines := line :: !lines
            done;
            parse_smt_model_q query (List.rev !lines)

        method get_collect_asserts = collect_asserts

        method set_collect_asserts b = collect_asserts <- b

        method get_unsat_cores =
            (* collect unsatisfiable cores *)
            let re = Str.regexp ".*unsat core ids: \\([ 0-9]+\\).*" in
            let cores = ref [] in
            self#append "(echo \"EOI\\n\")\n";
            let stop = ref false in
            while not !stop do
                let line = self#read_line in
                if Str.string_match re line 0
                then begin
                    let id_str = (Str.matched_group 1 line) in
                    let ids_as_str = (Str.split (Str.regexp " ") id_str) in
                    cores := (List.map int_of_string ids_as_str)
                end;

                stop := (line = "EOI")
            done;
            !cores

        method set_debug flag = debug <- flag

        method private is_out_sat ignore_errors =
            let l = self#read_line in
            (*printf "%s\n" l;*)
            match l with
            | "sat" -> true
            | "ok" -> true
            | "unsat" -> false
            | _ -> if ignore_errors
                then false
                else raise (Smt_error (sprintf "yices: %s" l))

        method private read_line =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            let out = PipeCmd.readline m_pipe_cmd in
            fprintf clog ";; READ: %s\n" out; flush clog;
            trace Trc.smt (fun _ -> sprintf "YICES: ^^^%s$$$\n" out);
            out

        method private append cmd =
            assert (not (PipeCmd.is_null m_pipe_cmd));
            if debug then printf "%s\n" cmd;
            self#write_line (sprintf "%s" cmd);
            fprintf clog "%s\n" cmd; flush clog

        method private append_assert s =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            self#append (sprintf "(assert %s)" s)

        method private write_line s =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            writeline m_pipe_cmd s

        method private sync =
            (* the solver can print more messages, thus, sync! *)
            self#append "(echo \"sync\\n\")";
            let stop = ref false in
            while not !stop do
                if "sync" = self#read_line then stop := true
            done
    end

