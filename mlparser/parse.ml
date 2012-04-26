open Lexing;;
open Printf;;

open Spin;;
open Spinlex;;
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
      | CONST i -> "CONST " ^ (string_of_int i)
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
      | RPAREN -> "RPAREN"
      | LPAREN -> "LPAREN"
      | RBRACE -> "RBRACE"
      | LBRACE -> "LBRACE"
      | RCURLY -> "RCURLY"
      | LCURLY -> "LCURLY"
      | DOT -> "DOT"
      | COMMA -> "COMMA"
      | COLON -> "COLON"
      | INCR -> "INCR"
      | DECR -> "DECR"
      | MOD -> "MOD"
      | DIV -> "DIV"
      | MINUS -> "MINUS"
      | UMIN -> "UMIN"
      | PLUS -> "PLUS"
      | MULT -> "MULT"
      | ASGN -> "ASGN"
      | BITNOT -> "BITNOT"
      | BITAND -> "BITAND"
      | BITOR -> "BITOR"
      | BITXOR -> "BITXOR"
      | AND -> "AND"
      | OR -> "OR"
      | NEG -> "NEG"
      | GE -> "GE"
      | LE -> "LE"
      | GT -> "GT"
      | LT -> "LT"
      | EQ -> "EQ"
      | NE -> "NE"
      | AT -> "AT"
      | LSHIFT -> "<<"
      | RSHIFT -> ">>"
      | VARREF -> "VARREF"
      | EOF -> "EOF"
;;


(* lexer function decorated by a preprocessor *)
let rec lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf =
    let tok = match !aux_bufs with
      [] -> lex_fun lexbuf  (* read from the main buffer *)

      | b :: tl -> (* read from the auxillary buffer *)
        let t = lex_fun b in
        if t != EOF then t
        else begin
            aux_bufs := tl;
            lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf
        end
    in
    match tok with
      (* TODO: handle macros with arguments foo(x, y) *)
      DEFINE(name, text) ->
        Hashtbl.add macro_tbl name text;
        lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf

      | NAME id ->
        if Hashtbl.mem macro_tbl id
        then (* substitute the contents and scan over it *)
            let newbuf = Lexing.from_string (Hashtbl.find macro_tbl id) in
            let bname = sprintf "%s:%d,%d" lexbuf.lex_curr_p.pos_fname
                lexbuf.lex_curr_p.pos_lnum
                (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol) in
            newbuf.lex_curr_p <- { newbuf.lex_curr_p with pos_fname = bname};
            aux_bufs := newbuf :: !aux_bufs;
            (* TODO: fail decently on co-recursive macro definitions *)
            lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf
        else tok

      | INCLUDE filename -> (* scan another file *)
        let path = (Filename.concat dirname filename) in
        let newbuf = Lexing.from_channel (open_in path) in
        newbuf.lex_curr_p <- { newbuf.lex_curr_p with pos_fname = filename };
        aux_bufs := newbuf :: !aux_bufs;
        lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf

      (* TODO: if/endif + ifdef/endif + if-else-endif*)
      | MACRO_IF | MACRO_IFDEF | MACRO_ELSE | MACRO_ENDIF ->
            raise (Failure (sprintf "%s is not supported" (token_s tok)))

      | MACRO_OTHER name ->
            raise (Failure (sprintf "#%s is not supported" name))

      | _ -> tok
;;


let _ =
    try
        let filename, basename, dirname =
        if Array.length Sys.argv > 1
        then Sys.argv.(1), Filename.basename Sys.argv.(1),
             Filename.dirname Sys.argv.(1)
        else raise (Failure "Use: program filename")
        in
        let lexbuf = Lexing.from_channel (open_in filename) in
        lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = basename };
        let lfun = lex_pp dirname (Hashtbl.create 10) (ref []) Spinlex.token in

        let res = Spin.program lfun lexbuf in
        printf "The outcome is %d\n" res; flush stdout

        (*
        let t = ref EQ in
        while !t != EOF do
            t := lfun lexbuf;
            printf "%s\n" (token_s !t)
        done
        *)
    with End_of_file ->
        print_string "Premature end of file\n";
        exit 1

