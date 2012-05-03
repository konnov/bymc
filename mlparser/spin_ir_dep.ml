(*
 * Here we collect functions that depend both on Spin_ir and Spin
 * to avoid circular dependencies between Spin and Spin_ir
 *)

open Printf;;

open Spin;;
open Spin_ir;;
open Spin_types;;

let token_s t =
    match t with
      ASSERT -> "ASSERT"
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
      | UNAME s -> "NAME " ^ s
      | PNAME s -> "NAME " ^ s
      | INAME s -> "NAME " ^ s
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
      | BITXOR -> " || "
      | AND -> " && "
      | OR -> " || "
      | NEG -> " ! "
      | GE -> ">="
      | LE -> "<="
      | GT -> ">"
      | LT -> "<"
      | EQ -> "=="
      | NE -> "!="
      | AT -> "@"
      | LSHIFT -> "<<"
      | RSHIFT -> ">>"
      | VARREF -> "VARREF"
      | EOF -> "EOF"
      | ASSUME -> "ASSUME"
      | SYMBOLIC -> "SYMBOLIC"
;;

let rec expr_s e =
    match e with
    | Nop -> "Nop"
    | Const i -> string_of_int i
    | Var v -> v#get_name
    | UnEx(tok, f) -> (token_s tok) ^ " " ^ (expr_s f)
    | BinEx(tok, f, g) ->  (expr_s f) ^ " " ^ (token_s tok) ^ " " ^ (expr_s g)
;;

let stmt_s s =
    match s with
    | Skip -> "skip"
    | Expr e -> sprintf "(%s)" (expr_s e)
    | Decl (v, e) ->
        sprintf "decl %s %s = %s"
            (var_type_s v#get_type) v#get_name (expr_s e)
    | Label l -> sprintf "%d: " l
    | Atomic_beg -> "atomic {"
    | Atomic_end -> "} /* atomic */"
    | D_step_beg -> "d_step {"
    | D_step_end -> "} /* d_step */"
    | Goto l -> sprintf "goto %d" l
    | Goto_unresolved ls -> sprintf "goto_unres %s" ls
    | If ls -> "if " ^ (List.fold_left (sprintf "%s %d") "" ls)
    | Else -> "else"
    | Assert e -> "assert " ^ (expr_s e)
    | Assume e -> "assume " ^ (expr_s e)
    | Print (s, es) ->
        sprintf "print \"%s\"%s" s
            (List.fold_left (fun a e -> a ^ ", " ^ (expr_s e)) "" es)

let prog_unit_s u =
    match u with
    | Proc p ->
        let h = (Printf.sprintf "proctype %s(...) {" p#get_name) in
        let ss = List.fold_left
            (fun a s -> a ^ "\n" ^ (stmt_s s)) "" p#get_stmts in
        h ^ ss ^ "\n}"

    | Stmt s -> (stmt_s s)
    | None -> Printf.sprintf "skip\n"
;;

