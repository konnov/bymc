{
(*
 * A lexer for threshold automata (see CONCUR'14, CAV'15 papers).
 * This is a temporary language that will most likely be replaced by
 * something more appropriate in the future.
 *
 * Igor Konnov, 2015
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
 | "skel"                { SKEL } 
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
 | ['0'-'9']+            { CONST (int_of_string (Lexing.lexeme lexbuf)) }
 | ['_' 'A'-'Z' 'a'-'z']['_' 'A'-'Z' 'a'-'z' '0'-'9']*
    {
        NAME (Lexing.lexeme lexbuf)
    }
 | eof                   { EOF }
 | _ as c { raise (Unexpected_token (sprintf "Unrecognized char: %c" c)) }

and comment = parse
 | "*/"                 { token lexbuf }
 | '\n'                 { new_line lexbuf; comment lexbuf }
 | _                    { comment lexbuf }
 | eof                  { raise End_of_file }

