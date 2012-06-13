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
      | ARRAY_DEREF -> "ARRAY_DEREF"
      | EOF -> "EOF"
      | ASSUME -> "ASSUME"
      | SYMBOLIC -> "SYMBOLIC"
;;

let rec expr_s e =
    match e with
    | Nop -> "nop"
    | Const i -> string_of_int i
    | Var v -> v#get_name
    | UnEx (tok, f) -> (token_s tok) ^ " " ^ (expr_s f)
    | BinEx (ARRAY_DEREF, arr, idx) ->
            sprintf "%s[%s]" (expr_s arr) (expr_s idx)
    | BinEx (tok, f, g) ->  (expr_s f) ^ " " ^ (token_s tok) ^ " " ^ (expr_s g)
;;

let op_of_expr e =
    match e with
    | UnEx (tok, _) -> tok
    | BinEx (tok, _, _) -> tok
    | _ -> EOF
;;

let stmt_s s =
    match s with
    | Skip _ -> "skip"
    | Expr (_, e) -> sprintf "(%s)" (expr_s e)
    | Decl (_, v, e) ->
        sprintf "decl %s %s %s = %s"
            v#flags_s (var_type_s v#get_type) v#get_name (expr_s e)
    | Label (_, l) -> sprintf "%d: " l
    | Atomic_beg _ -> "atomic {"
    | Atomic_end _ -> "} /* atomic */"
    | D_step_beg _ -> "d_step {"
    | D_step_end _ -> "} /* d_step */"
    | Goto (_, l) -> sprintf "goto %d" l
    | If (_, ls, exitl) ->
        sprintf "if %s -> %d" (List.fold_left (sprintf "%s %d") "" ls) exitl
    | Else _ -> "else"
    | Assert (_, e) -> "assert " ^ (expr_s e)
    | Assume (_, e) -> "assume " ^ (expr_s e)
    | Print (_, s, es) ->
        sprintf "print \"%s\"%s" s
            (List.fold_left (fun a e -> a ^ ", " ^ (expr_s e)) "" es)
;;

let rec mir_stmt_s s =
    let seq_s seq = 
        List.fold_left (fun t s -> t ^ (mir_stmt_s s) ^ "\n") "" seq
    in
    match s with
    | MSkip id -> sprintf "<%3d> skip" id
    | MExpr (id, e) -> sprintf "<%3d> (%s)" id (expr_s e)
    | MDecl (id, v, e) ->
        sprintf "<%3d> decl %s %s %s = %s"
            id v#flags_s (var_type_s v#get_type) v#get_name (expr_s e)
    | MLabel (id, l) -> sprintf "<%3d> %d: " id l
    | MAtomic (id, stmts) ->
        (sprintf "<%3d> atomic {\n" id) ^ (seq_s stmts) ^ "}"
    | MD_step (id, stmts) ->
        (sprintf "<%3d> d_step {\n" id) ^ (seq_s stmts) ^ "}"
    | MGoto (id, l) -> sprintf "<%3d> goto %d" id l
    | MIf (id, opts) ->
        sprintf "<%3d> if\n" id
        ^
        (List.fold_left
            (fun t o ->
                match o with
                | MOptGuarded seq -> "  :: " ^ (seq_s seq)
                | MOptElse seq -> "  :: else -> " ^ (seq_s seq)
            ) "" opts)
        ^
        "fi"
    | MAssert (id, e) -> sprintf "<%3d> assert %s" id (expr_s e)
    | MAssume (id, e) -> sprintf "<%3d> assume %s" id (expr_s e)
    | MPrint (id, s, es) ->
        sprintf "<%3d> print \"%s\"%s"
            id s (List.fold_left (fun a e -> a ^ ", " ^ (expr_s e)) "" es)

let prog_unit_s u =
    match u with
    | Proc p ->
        let act = if p#get_active_expr <> (Const 0)
            then Printf.sprintf "active[%s] " (expr_s p#get_active_expr)
            else "" in
        let args = List.fold_left
            (fun a arg -> Printf.sprintf
                "%s %s %s;" a (var_type_s arg#get_type) arg#get_name)
            "" p#get_args in
        let h = (Printf.sprintf "%sproctype %s(%s) {" act p#get_name args) in
        let ss = List.fold_left
            (fun a s -> a ^ "\n" ^ (mir_stmt_s s)) "" p#get_stmts in
        h ^ ss ^ "\n}"

    | Stmt s -> mir_stmt_s s
    | None -> Printf.sprintf "skip\n"
;;

