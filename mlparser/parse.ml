open Spin;;
open Spinlex;;
open Spin_types;;
open Printf;;

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
      | DOT -> "DOT"
      | COMMA -> "COMMA"
      | COLON -> "COLON"
      | INCR -> "INCR"
      | DECR -> "DECR"
      | MOD -> "MOD"
      | DIV -> "DIV"
      | MINUS -> "MINUS"
      | PLUS -> "PLUS"
      | MULT -> "MULT"
      | ASGN -> "ASGN"
      | BITAND -> "BITAND"
      | BITOR -> "BITOR"
      | AND -> "AND"
      | OR -> "OR"
      | GE -> "GE"
      | LE -> "LE"
      | GT -> "GT"
      | LT -> "LT"
      | EQ -> "EQ"
      | NE -> "NE"
;;


(* lexer function decorated by a preprocessor *)
let rec lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf =
    let tok = match !aux_bufs with
      [] -> lex_fun lexbuf  (* read from the main buffer *)

      | b :: tl -> (* read from the auxillary buffer *)
          try
              lex_fun b    
          with End_of_file ->
              aux_bufs := tl;
              lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf
    in
    match tok with
      DEFINE(name, text) ->
        Hashtbl.add macro_tbl name text;
        lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf

      | NAME id ->
        if Hashtbl.mem macro_tbl id
        then (* substitute the contents and scan over it *)
            let new_buf = Lexing.from_string (Hashtbl.find macro_tbl id) in
            aux_bufs := new_buf :: !aux_bufs;
            (* TODO: it must fail properly on co-recursive macro definitions *)
            lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf
        else tok

      | INCLUDE filename -> (* scan another file *)
        let path = (Filename.concat dirname filename) in
        let new_buf = Lexing.from_channel (open_in path) in
        aux_bufs := new_buf :: !aux_bufs;
        lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf

      (* TODO: if/endif + ifdef/endif *)

      | _ -> tok
;;


let _ =
    try
        let filename, dirname = if Array.length Sys.argv > 1
        then Sys.argv.(1), Filename.dirname Sys.argv.(1)
        else raise (Failure "Use: program filename")
        in
        let lexbuf = Lexing.from_channel (open_in filename) in
        let lfun = lex_pp dirname (Hashtbl.create 10) (ref []) Spinlex.token in
        (*
        let _ = Spin.program lfun lexbuf in ()
        *)
        while true do
            let t = lfun lexbuf in
            printf "%s\n" (token_s t)
        done
    with End_of_file ->
        exit 0

