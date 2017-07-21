{
(*
 * A lexer for threshold automata (see CONCUR'14, CAV'15 papers).
 * This is a temporary language that will most likely be replaced by
 * something more appropriate in the future.
 *
 * Since we started to use threshold automata as an input for synthesis,
 * we have extended their syntax with unknowns, unchanged, define, etc.
 *
 * Igor Konnov, 2015-2017
 *)
open Printf

(*
open SpinTypes
*)
open Ta

exception Unexpected_token of string


let string_chars s = String.sub s 1 ((String.length s) - 2)

let new_line lexbuf =
    (* backport of Lexing.new_line to ocaml 3.10.2 *)
    (* this function is copied from the implementation found in 3.12.1 *)
    let lcp = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- {
        lcp with
            Lexing.pos_lnum = lcp.Lexing.pos_lnum + 1;
            Lexing.pos_bol = lcp.Lexing.pos_cnum;
    }

let token_s = function
    | LTLF -> "LTLF"
    | LTLG -> "LTLG"
    | NOT -> "NOT"
    | AND -> "AND"
    | OR -> "OR"
    | PLUS -> "PLUS"
    | IMPLIES -> "IMPLIES"
    | MINUS -> "MINUS"
    | MULT -> "MULT"
    | NE -> "NE"
    | EQ -> "EQ"
    | LT -> "LT"
    | GT -> "GT"
    | LE -> "LE"
    | GE -> "GE"
    | TRUE -> "TRUE"
    | COMMA -> "COMMA"
    | LPAREN -> "LPAREN"
    | RPAREN -> "RPAREN"
    | LBRACE -> "LBRACE"
    | RBRACE -> "RBRACE"
    | LCURLY -> "LCURLY"
    | RCURLY -> "RCURLY"
    | COLON -> "COLON"
    | SEMI -> "SEMI"
    | PRIME -> "PRIME"
    | SKEL -> "SKEL"
    | THRESHAUTO -> "threshAuto"
    | ASSUME -> "ASSUME"
    | SPECIFICATIONS -> "SPECIFICATIONS"
    | DO -> "DO"
    | INITS -> "INITS"
    | LOCAL -> "LOCAL"
    | LOCATIONS -> "LOCATIONS"
    | PARAMETERS -> "PARAMETERS"
    | UNKNOWNS -> "UNKNOWNS"
    | RULES -> "RULES"
    | SHARED -> "SHARED"
    | WHEN -> "WHEN"
    | CONST i -> "CONST" (*Printf.sprintf "CONST(%d)" i*)
    | NAME n -> "NAME" (*Printf.sprintf "NAME(%s)" n*)
    | MACRO n -> "MACRO" (*Printf.sprintf "NAME(%s)" n*)
    | DEFINE -> "define" (*Printf.sprintf "NAME(%s)" n*)
    | UNCHANGED -> "UNCHANGED"
    | EOF -> "EOF"

}


rule token = parse
   [' ' '\t']+           { token lexbuf } (* skip spaces *)
 | '\n'                  { new_line lexbuf; token lexbuf }
 | "/*"                  { comment lexbuf }
 | "<>"                  { LTLF }
 | "[]"                  { LTLG }
 | '!'                   { NOT }
 | "&&"                  { AND }
 | "||"                  { OR }
 | '+'                   { PLUS }
 | "->"                  { IMPLIES }
 | '-'                   { MINUS }
 | '*'                   { MULT }
 | "!="                  { NE }
 | "=="                  { EQ }
 | '<'                   { LT }
 | '>'                   { GT }
 | "<="                  { LE }
 | ">="                  { GE }
 | ','                   { COMMA }
 | '('                   { LPAREN }
 | ')'                   { RPAREN }
 | '['                   { LBRACE }
 | ']'                   { RBRACE }
 | '{'                   { LCURLY }
 | '}'                   { RCURLY }
 | ':'                   { COLON }
 | ';'                   { SEMI }
 | '''                   { PRIME }
 | "true"                { TRUE } 
 | "skel"                { SKEL } 
 | "threshAuto"          { THRESHAUTO } 
 | "assumptions"         { ASSUME } 
 | "specifications"      { SPECIFICATIONS } 
 | "do"                  { DO }
 | "inits"               { INITS }
 | "local"               { LOCAL }
 | "locations"           { LOCATIONS } 
 | "parameters"          { PARAMETERS } 
 | "unknowns"            { UNKNOWNS } 
 | "rules"               { RULES } 
 | "shared"              { SHARED } 
 | "when"                { WHEN } 
 | "unchanged"           { UNCHANGED } 
 | "define"              { DEFINE } 
 | ['0'-'9']+            { CONST (int_of_string (Lexing.lexeme lexbuf)) }
 (* an identifier is either one capital letter (for backward compatibility),
    or it should have at least one small letter *)
 | ['_' 'A'-'Z']*['a'-'z']['_' 'A'-'Z' 'a'-'z' '0'-'9']*
    {
        NAME (Lexing.lexeme lexbuf)
    }
 | ['A'-'Z']
    {
        NAME (Lexing.lexeme lexbuf)
    }
 (* a macro should have at least two characters, starting with a capital letter
    and containing only capitals and digits
  *)
 | ['_' 'A'-'Z']['_' 'A'-'Z' '0'-'9']+
    {
        MACRO (Lexing.lexeme lexbuf)
    }
 | eof                   { EOF }
 | _ as c { raise (Unexpected_token (sprintf "Unrecognized char: %c" c)) }

and comment = parse
 | "*/"                 { token lexbuf }
 | '\n'                 { new_line lexbuf; comment lexbuf }
 | _                    { comment lexbuf }
 | eof                  { raise End_of_file }

