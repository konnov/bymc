open Printf

open Accums
open Spin
open SpinIr
open SpinIrImp
open SpinTypes

exception Smv_error of string

let var_type_smv tp =
    let base_str = function
      | TBIT -> "boolean"
      | TBYTE -> "boolean"
      | TSHORT -> "integer"
      | TINT -> "integer"
      | TUNSIGNED -> raise (Smv_error "Unsigned is not supported")
      | TCHAN -> raise (Smv_error "Unsigned is not supported")
      | TMTYPE -> raise (Smv_error "Unsigned is not supported") 
      | TPROPOSITION -> raise (Smv_error "Unsigned is not supported")
      | TUNDEF -> raise (Failure "Undefined type")
    in
    let l, r = tp#range in
    if not tp#is_array && tp#has_range
    then sprintf "{ %s }" (str_join ", " (List.map string_of_int (range l r)))
    else base_str tp#basetype


let type_default_smv tp =
    match tp#basetype with
      | TBIT -> "FALSE"
      | TBYTE -> "0"
      | TSHORT -> "0"
      | TINT -> "0"
      | TUNSIGNED -> raise (Smv_error "Unsigned is not supported")
      | TCHAN -> raise (Smv_error "Unsigned is not supported")
      | TMTYPE -> raise (Smv_error "Unsigned is not supported") 
      | TPROPOSITION -> raise (Smv_error "Unsigned is not supported")
      | TUNDEF -> raise (Failure "Undefined type")


let token_s t =
    match t with
      | ASSERT -> "ASSERT"
      | PRINT -> "PRINT"
      | PRINTM -> "PRINTM"
      | C_CODE -> "C_CODE"
      | C_DECL -> "C_DECL"
      | C_EXPR -> "C_EXPR"
      | C_STATE -> "C_STATE"
      | C_TRACK -> "C_TRACK"
      | RUN -> "RUN"
      | LEN -> "LEN"
      | ENABLED -> "ENABLED"
      | EVAL -> "EVAL"
      | PC_VAL -> "PC_VAL"
      | TYPEDEF -> "TYPEDEF"
      | MTYPE -> "MTYPE"
      | INLINE -> "INLINE"
      | LABEL -> "LABEL"
      | OF -> "OF"
      | GOTO -> "GOTO"
      | BREAK -> "BREAK"
      | ELSE -> "ELSE"
      | SEMI -> "SEMI"
      | IF -> "IF"
      | FI -> "FI"
      | DO -> "DO"
      | OD -> "OD"
      | FOR -> "FOR"
      | SELECT -> "SELECT"
      | IN -> "IN"
      | SEP -> "SEP"
      | DOTDOT -> "DOTDOT"
      | ATOMIC -> "ATOMIC"
      | NON_ATOMIC -> "NON_ATOMIC"
      | D_STEP -> "D_STEP"
      | UNLESS -> "UNLESS"
      | TIMEOUT -> "TIMEOUT"
      | NONPROGRESS -> "NONPROGRESS"
      | ACTIVE -> "ACTIVE"
      | PROCTYPE -> "PROCTYPE"
      | D_PROCTYPE -> "D_PROCTYPE"
      | HIDDEN -> "HIDDEN"
      | SHOW -> "SHOW"
      | ISLOCAL -> "ISLOCAL"
      | PRIORITY -> "PRIORITY"
      | PROVIDED -> "PROVIDED"
      | FULL -> "FULL"
      | EMPTY -> "EMPTY"
      | NFULL -> "NFULL"
      | NEMPTY -> "NEMPTY"
      | CONST i -> (string_of_int i)
      | TYPE tp -> "TYPE" ^ (var_type_s tp)
      | XU tp -> (xu_type_s tp)
      | NAME s -> "NAME " ^ s
      | UNAME s -> "UNAME " ^ s
      | PNAME s -> "PNAME " ^ s
      | INAME s -> "INAME " ^ s
      | FNAME s -> "FNAME " ^ s
      | STRING s -> "STRING " ^ s
      | CLAIM -> "CLAIM"
      | TRACE -> "TRACE"
      | INIT -> "INIT"
      | LTL -> "LTL"
      | DEFINE(n, v) -> (sprintf "DEFINE %s '%s'" n v)
      | INCLUDE(filename) -> (sprintf "INCLUDE \"%s\"" filename)
      | MACRO_IF -> "MACRO_IF"
      | MACRO_IFDEF -> "MACRO_IFDEF"
      | MACRO_ELSE -> "MACRO_ELSE"
      | MACRO_ENDIF -> "MACRO_ENDIF"
      | MACRO_OTHER name -> (sprintf "#%s" name)
      | NOTRACE -> "NOTRACE"
      | NEVER -> "NEVER"
      | R_RCV -> "R_RCV"
      | RCV -> "RCV"
      | SND -> "SND"
      | O_SND -> "O_SND"
      | RPAREN -> ")"
      | LPAREN -> "("
      | RBRACE -> "]"
      | LBRACE -> "["
      | RCURLY -> "}"
      | LCURLY -> "{"
      | DOT -> "."
      | COMMA -> ","
      | COLON -> ":"
      | INCR -> "++"
      | DECR -> "--"
      | MOD -> "%"
      | DIV -> "/"
      | MINUS -> "-"
      | UMIN -> "(-)"
      | PLUS -> "+"
      | MULT -> "*"
      | ASGN -> "="
      | BITNOT -> "~"
      | BITAND -> " & "
      | BITOR -> " | "
      | BITXOR -> " | "
      | AND -> " & "
      | OR -> " | "
      | NEG -> " ! "
      | GE -> ">="
      | LE -> "<="
      | GT -> ">"
      | LT -> "<"
      | EQ -> "="
      | NE -> "!="
      | AT -> "@"
      | LSHIFT -> "<<"
      | RSHIFT -> ">>"
      | VARREF -> "VARREF"
      | ARR_ACCESS -> "ARR_ACCESS"
      | ARR_UPDATE -> "ARR_UPDATE"
      | ALWAYS -> " G "
      | EVENTUALLY -> " F "
      | UNTIL -> " U "
      | RELEASE -> " V "
      | WEAK_UNTIL -> " W "
      | NEXT -> " X "
      | IMPLIES -> "->"
      | EQUIV -> "<->"
      | EOF -> "EOF"
      | ASSUME -> "ASSUME"
      | SYMBOLIC -> "SYMBOLIC"
      | ALL -> "all"
      | SOME -> "some"
      | CARD -> "card"
      | POR -> "or"
      | PAND -> "and"

(* we need var_fun as variables can look either x or next(x) *)
let expr_s var_fun e =
    let rec to_s = function
    | Nop comment -> sprintf "-- %s" comment
    | Const i -> string_of_int i
    | Var v -> var_fun v
    | UnEx (CARD, f) -> sprintf "card(%s)" (to_s f)
    | UnEx (tok, f) -> sprintf "(%s%s)" (token_s tok) (to_s f)
    | BinEx (ARR_ACCESS, arr, idx) ->
            sprintf "%s[%s]" (to_s arr) (to_s idx)
    (* XXX: not well defined *)
    | BinEx (ASGN, Var arr,
                BinEx (ARR_UPDATE, BinEx (ARR_ACCESS, Var old_arr, idx), rhs))
        ->
            sprintf "%s<-%s[%s] = %s" arr#get_name
                old_arr#get_name (to_s idx) (to_s rhs)
    | BinEx (AND, f, g) -> sprintf "(%s & %s)" (to_s f) (to_s g)
    | BinEx (OR, f, g) -> sprintf "(%s | %s)" (to_s f) (to_s g)
    | BinEx (ASGN, f, g) -> sprintf "%s == %s" (to_s f) (to_s g)
    | BinEx (AT, proc, lab) -> sprintf "%s@%s" (to_s proc) (to_s lab)
    | BinEx (tok, f, g) ->
        sprintf "(%s %s %s)" (to_s f) (token_s tok) (to_s g)
    | Phi (lhs, rhs) ->
        let rhs_s = String.concat ", " (List.map (fun v -> v#get_name) rhs)
        in
        sprintf "%s = phi(%s)" lhs#get_name rhs_s
    | LabelRef (proc_name, lab_name) ->
        sprintf "%s@%s" proc_name lab_name
    in
    to_s e

