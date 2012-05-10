(* utility functions to integrate with Yices *)

open Printf;;

open Spin_ir;;
open Spin_ir_imp;;

let rec var_to_smt var =
    let ts = match var#get_type with
    | TBIT -> "bool"
    | TBYTE -> "int"
    | TSHORT -> "int"
    | TINT -> "int"
    | TUNSIGNED -> "nat"
    | TCHAN -> raise (Failure "Type chan is not supported")
    | TMTYPE -> raise (Failure "Type mtype is not supported")
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
        | MOD   -> sprintf "(% %s %s)" (expr_to_smt l) (expr_to_smt r)
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
