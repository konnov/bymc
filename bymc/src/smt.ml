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
exception Communication_failure of string

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
        | ARR_ACCESS -> sprintf "(%s %s)" (expr_to_smt l) (expr_to_smt r)
        | _ -> raise (Failure
                (sprintf "No idea how to translate %s to SMT" (token_s tok)))
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
                sprintf "(subrange %d %d)" l r
            else base_type
        in
        if tp#is_array
        then sprintf "(-> (subrange 0 %d) %s)" (tp#nelems - 1) subtype
        else subtype
    in
    sprintf "(define %s :: %s)" var#mangled_name complex_type


(* The interface to the SMT solver (yices).
   We are using the text interface, as it is way easier to debug. *)
class yices_smt =
    object(self)
        (* for how long we wait for output from yices if check is issued *)
        val check_timeout_sec = 3600.0
        (* for how long we wait for output from yices if another command is issued*)
        val timeout_sec = 10.0
        val mutable pid = 0
        val mutable clog = stdout
        val m_pipe_cmd: PipeCmd.cmd_stat =
            PipeCmd.create "yices" [||] "yices.err"
        val mutable debug = false
        val mutable collect_asserts = false
        val mutable poll_tm_sec = 10.0
        val mutable m_pushes = 0

        method start =
            clog <- open_out "yices.log";
            self#append "(set-verbosity! 2)\n" (* to track assert+ *)
        
        method stop =
            close_out clog;
            PipeCmd.destroy m_pipe_cmd

        method write_line s =
            writeline m_pipe_cmd s

        method read_line =
            let out = PipeCmd.readline m_pipe_cmd in
            fprintf clog ";; READ: %s\n" out; flush clog;
            log Debug.TRACE (sprintf "YICES: ^^^%s$$$\n" out);
            out

        method append cmd =
            if debug then printf "%s\n" cmd;
            self#write_line (sprintf "%s" cmd);
            fprintf clog "%s\n" cmd; flush clog

        method append_assert s =
            self#append (sprintf "(assert %s)" s)

        method append_var_def (v: var) (tp: data_type) =
            self#append (var_to_smt v tp)

        method comment (line: string) =
            self#append (";; " ^ line)

        method append_expr expr =
            let eid = ref 0 in
            let e_s = (expr_to_smt expr) in
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
            m_pushes <- m_pushes + 1;
            self#append "(push)"

        method pop_ctx =
            if m_pushes = 0
            then raise (Failure ("pop: yices stack is empty!"));
            m_pushes <- m_pushes - 1;
            self#append "(pop)"

        method sync =
            (* the solver can print more messages, thus, sync! *)
            self#append "(echo \"sync\\n\")";
            let stop = ref false in
            while not !stop do
                if "sync" = self#read_line then stop := true
            done

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

        method set_need_evidence b =
            if b
            then self#append "(set-evidence! true)"
            else self#append "(set-evidence! false)"

        method get_evidence =
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
            List.rev !lines

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

        method is_out_sat ignore_errors =
            let l = self#read_line in
            (*printf "%s\n" l;*)
            match l with
            | "sat" -> true
            | "ok" -> true
            | "unsat" -> false
            | _ -> if ignore_errors
                then false
                else raise (Smt_error (sprintf "yices: %s" l))

        method set_debug flag = debug <- flag
    end
;;

