(* utility functions to integrate with Yices *)

open Printf;;

open Spin_types;;
open Spin;;
open Spin_ir;;
open Spin_ir_imp;;

exception Smt_error of string;;

(* the wrapper of the actual solver (yices) *)
class yices_smt =
    object(self)
        val mutable pid = 0
        val mutable cin = stdin
        val mutable cout = stdout
        val mutable debug = false

        method start =
            let pin, pout = Unix.open_process "yices" in
            cin <- pin;
            cout <- pout
        
        method stop =
            Unix.close_process (cin, cout)

        method append cmd =
            if debug then printf "%s\n" cmd;
            fprintf cout "%s\n" cmd

        method push_ctx = fprintf cout "(push)\n"

        method pop_ctx = fprintf cout "(pop)\n"

        method check =
            fprintf cout "(status)\n"; (* it can be unsat already *)
            flush cout;
            if not (self#is_out_sat true)
            then false
            else begin
                fprintf cout "(check)\n";
                flush cout;
                self#is_out_sat false
            end

        method is_out_sat ignore_errors =
            let l = input_line cin in
            match l with
            | "sat" -> true
            | "ok" -> true
            | "unsat" -> false
            | _ -> if ignore_errors
                then false
                else raise (Smt_error (sprintf "yices: %s" l))

        method get_cin = cin
        method get_cout = cout
    end
;;

let rec var_to_smt var =
    let ts = match var#get_type with
    | TBIT -> "bool"
    | TBYTE -> "int"
    | TSHORT -> "int"
    | TINT -> "int"
    | TUNSIGNED -> "nat"
    | TCHAN -> raise (Failure "Type chan is not supported")
    | TMTYPE -> raise (Failure "Type mtype is not supported")
    in
    sprintf "(define %s :: %s)" var#get_name ts
;;

let rec expr_to_smt e =
    match e with
    | Nop -> ""
    | Const i -> string_of_int i
    | Var v -> v#get_name
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
        | DIV   -> sprintf "(/ %s %s)" (expr_to_smt l) (expr_to_smt r)
        | MOD   -> sprintf "(%% %s %s)" (expr_to_smt l) (expr_to_smt r)
        | GT    -> sprintf "(> %s %s)" (expr_to_smt l) (expr_to_smt r)
        | LT    -> sprintf "(< %s %s)" (expr_to_smt l) (expr_to_smt r)
        | GE    -> sprintf "(>= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | LE    -> sprintf "(<= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | EQ    -> sprintf "(== %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | NE    -> sprintf "(!= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | AND   -> sprintf "(and %s %s)" (expr_to_smt l) (expr_to_smt r)
        | OR    -> sprintf "(or %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | _ -> raise (Failure
                (sprintf "No idea how to translate %s to SMT" (token_s tok)))
        end
;;
