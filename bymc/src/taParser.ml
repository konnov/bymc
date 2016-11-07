open Batteries
open Lexing

open Spinlex

exception ParseErr of string

let position_s lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf
    "%s:%d:%d" pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)


let lex_pp lexfun buf =
    let tok = lexfun buf in
    (* (* uncomment to debug (you can feed the stream to menhir --interpret): *)
    Printf.printf "%s " (Talex.token_s tok);
    *)
    tok


let parse_input name input =
    let buf = Lexing.from_input input in
    buf.lex_curr_p <- { buf.lex_curr_p with pos_fname = name };
    SpinParserState.reset_state ();
    try Ta.start (lex_pp Talex.token) buf with
    | Spinlex.Unexpected_token msg ->
        raise (ParseErr (Printf.sprintf "%s%!\n" msg))

    | TaErr.SyntaxErr msg ->
        raise (ParseErr (Printf.sprintf "%s: %s%!\n" (position_s buf) msg))

    | TaErr.SemanticErr msg ->
        raise (ParseErr (Printf.sprintf "%s%!\n" msg))

    | Ta.Error ->
        raise (ParseErr ((position_s buf) ^ "%s: syntax error\n"))


let parse_file filename =
    let input = open_in filename in
    let res = parse_input filename input in
    IO.close_in input;
    res

