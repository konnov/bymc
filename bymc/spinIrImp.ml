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
      | ARR_ACCESS -> "ARR_ACCESS"
      | ARR_UPDATE -> "ARR_UPDATE"
      | EOF -> "EOF"
      | ASSUME -> "ASSUME"
      | SYMBOLIC -> "SYMBOLIC"
      | ALL -> "all"
      | SOME -> "some"
      | CARD -> "card"
;;

let rec expr_s e =
    match e with
    | Nop comment -> sprintf "skip /* %s */" comment
    | Const i -> string_of_int i
    | Var v -> v#get_name
    | UnEx (CARD, f) -> sprintf "card(%s)" (expr_s f)
    | UnEx (tok, f) -> sprintf "(%s%s)" (token_s tok) (expr_s f)
    | BinEx (ARR_ACCESS, arr, idx) ->
            sprintf "%s[%s]" (expr_s arr) (expr_s idx)
    | BinEx (ASGN, Var arr,
                BinEx (ARR_UPDATE, BinEx (ARR_ACCESS, Var old_arr, idx), rhs)) ->
            sprintf "%s<-%s[%s] = %s" arr#get_name
                old_arr#get_name (expr_s idx) (expr_s rhs)
    | BinEx (AND, f, g) -> sprintf "(%s && %s)" (expr_s f) (expr_s g)
    | BinEx (OR, f, g) -> sprintf "(%s || %s)" (expr_s f) (expr_s g)
    | BinEx (ASGN, f, g) -> sprintf "%s = %s" (expr_s f) (expr_s g)
    | BinEx (tok, f, g) ->
        sprintf "(%s %s %s)" (expr_s f) (token_s tok) (expr_s g)
    | Phi (lhs, rhs) ->
            let rhs_s = String.concat ", " (List.map (fun v -> v#get_name) rhs)
            in
            sprintf "%s = phi(%s)" lhs#get_name rhs_s
;;

let op_of_expr e =
    match e with
    | UnEx (tok, _) -> tok
    | BinEx (tok, _, _) -> tok
    | _ -> EOF
;;

let stmt_s s =
    match s with
    | Skip id -> sprintf "<%3d> skip" id
    | Expr (id, e) -> sprintf "<%3d> (%s)" id (expr_s e)
    | Decl (id, v, e) ->
        sprintf "<%3d> decl %s %s %s = %s"
            id v#flags_s (var_type_s v#get_type) v#get_name (expr_s e)
    | Label (id, l) -> sprintf "<%3d> %d: " id l
    | Atomic_beg id -> sprintf "<%3d> atomic {" id
    | Atomic_end id -> sprintf "<%3d> } /* atomic */" id
    | D_step_beg id -> sprintf "<%3d> d_step {" id
    | D_step_end id -> sprintf "<%3d> } /* d_step */" id
    | Goto (id, l) -> sprintf "<%3d> goto %d" id l
    | If (id, ls, exitl) ->
        sprintf "<%3d> if %s -> %d"
            id (List.fold_left (sprintf "%s %d") "" ls) exitl
    | Assert (id, e) -> sprintf "<%3d> assert %s" id (expr_s e)
    | Assume (id, e) -> sprintf "<%3d> assume %s" id (expr_s e)
    | Havoc (id, v) -> sprintf "<%3d> havoc %s" id v#get_name
    | Print (id, s, es) ->
        sprintf "<%3d> print \"%s\"%s" id s
            (List.fold_left (fun a e -> a ^ ", " ^ (expr_s e)) "" es)
;;

let mir_to_lir (stmts: 't mir_stmt list) : 't stmt list =
    let mk_else_cond options =
        let get_guard e = function
        | MOptGuarded (MExpr (_, g) :: _) ->
              if not_nop e
              then BinEx (AND, e, UnEx (NEG, g))
              else UnEx (NEG, g)
        | MOptElse _ -> e
        | _ -> raise (Failure ("If option is not protected by a guard"))
        in
        MExpr (-1, List.fold_left get_guard (Nop "") options)
    in
    let rec make_one s tl =
        match s with
        | MIf (id, options) ->
            let exit_lab = mk_uniq_label () in
            let labs_seqs = List.map (make_option options exit_lab) options in
            let opt_labs, opt_seqs = List.split labs_seqs in
            If (id, opt_labs, exit_lab)
                :: ((List.concat opt_seqs) @ (Label (-1, exit_lab) :: tl))
        | MAtomic (id, seq) ->
            let new_seq = List.fold_right make_one seq [] in
            Atomic_beg id :: new_seq @ Atomic_end (-1) :: tl
        | MD_step (id, seq) ->
            let new_seq = List.fold_right make_one seq [] in
            D_step_beg id :: new_seq @ D_step_end (-1) :: tl
        | MGoto (id, i) -> Goto (id, i) :: tl
        | MLabel (id, i) -> Label (id, i) :: tl
        | MDecl (id, v, i) -> Decl (id, v, i) :: tl
        | MExpr (id, e) -> Expr (id, e) :: tl
        | MSkip id -> Skip id :: tl
        | MAssert (id, e) -> Assert (id, e) :: tl
        | MAssume (id, e) -> Assume (id, e) :: tl
        | MPrint (id, s, args) -> Print (id, s, args) :: tl
        | MHavoc (id, v) -> Havoc (id, v) :: tl
        | MUnsafe (id, s) -> Expr (id, Nop "") :: tl
        | MDeclProp (id, _, _) -> Expr (id, Nop "") :: tl
    and
        make_option all_options exit_lab opt =
        let seq = match opt with
            | MOptGuarded sts -> sts
            | MOptElse sts -> (mk_else_cond all_options) :: sts
        in
        let opt_lab = mk_uniq_label () in
        let body = List.fold_right make_one seq [] in
        let new_seq = ((Label (-1, opt_lab) :: body) @ [Goto (-1, exit_lab)]) in
        (opt_lab, new_seq)
    in
    let lstmts = List.fold_right make_one stmts [] in
    (* assign unique negative ids instead of just -1's *)
    let _, res = List.fold_right
        (fun s (min_id, tl) ->
            let s_id = stmt_id s in
            if s_id = -1
            then (min_id - 1, (replace_stmt_id min_id s) :: tl)
            else (min_id, s :: tl)
        ) lstmts (-1, []) 
    in
    res
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
    | MDeclProp (id, v, PropAll e) ->
            sprintf "<%3d> prop %s = all %s" id v#get_name (expr_s e)
    | MDeclProp (id, v, PropSome e) ->
            sprintf "<%3d> prop %s = some %s" id v#get_name (expr_s e)
    | MDeclProp (id, v, PropGlob e) ->
            sprintf "<%3d> prop %s = glob %s" id v#get_name (expr_s e)
    | MLabel (id, l) -> sprintf "<%3d> %d: " id l
    | MAtomic (id, stmts) ->
        sprintf "<%3d> atomic {\n%s\n }" id (seq_s stmts)
    | MD_step (id, stmts) ->
        sprintf "<%3d> d_step {\n%s\n }" id (seq_s stmts)
    | MGoto (id, l) -> sprintf "<%3d> goto %d" id l
    | MIf (id, opts) ->
        let inner = (List.fold_left
            (fun t o ->
                match o with
                | MOptGuarded seq -> "  :: " ^ (seq_s seq)
                | MOptElse seq -> "  :: else -> " ^ (seq_s seq)
            ) "" opts)
        in
        sprintf "<%3d> if\n%s\n fi" id inner
    | MAssert (id, e) -> sprintf "<%3d> assert %s" id (expr_s e)
    | MAssume (id, e) -> sprintf "<%3d> assume %s" id (expr_s e)
    | MHavoc (id, v) -> sprintf "<%3d> havoc %s" id v#get_name
    | MUnsafe (id, s) -> sprintf "<%3d> %s" id s
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

