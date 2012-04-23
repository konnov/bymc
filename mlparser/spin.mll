{
    open spin_types;;
    
    exception Unexpected_token of string

    errrrrrorrr

    let string_chars s = String.sub s 1 ((String.length s)-2) ;;
    let pp_word s = String.sub s 1 ((String.length s)-1) ;;
    let nn n t v s = { s = n; tok = t; v = v; sym = s };; 
}

rule token = parse
 | eof                   { raise End_of_file }
 | [' ' '\t' '\n']+      { token lexbuf } (* skip spaces *)
 | "/*"                  { comment lexbuf }
 | "!="                  { NE }
 | "!!"                  { O_SND }
 | '!'                   { SND }
 | "??"                  { R_RCV }
 | '?'                   { RCV }
 | '&'                   { (Lexing.lexeme lexbuf) }
 | '|'                   { (Lexing.lexeme lexbuf) }
 | "=="                  { EQ }
 | '='                   { ASGN }
 | "&&"                  { AND }
 | '&'                   { (Lexing.lexeme lexbuf) }
 | "||"                  { OR }
 | '|'                   { (Lexing.lexeme lexbuf) }
 | '%'                   { (Lexing.lexeme lexbuf) }
 | '+'                   { (Lexing.lexeme lexbuf) }
 | "--"                  { DECR }
 | "->"                  { SEMI }
 | ';'                   { SEMI }
 | '-'                   { (Lexing.lexeme lexbuf) }
 | '*'                   { (Lexing.lexeme lexbuf) }
 | '/'                   { (Lexing.lexeme lexbuf) }
 | "::"                  { SEP }
 | ':'                   { (Lexing.lexeme lexbuf) }
 | ['<' '>']             { (Lexing.lexeme lexbuf) }
 | "<="                  { (Lexing.lexeme lexbuf) }
 | ">="                  { (Lexing.lexeme lexbuf) }
 | ".."                  { DOTDOT }
 | '.'                   { (Lexing.lexeme lexbuf) }
 | '('                   { (Lexing.lexeme lexbuf) }
 | ')'                   { (Lexing.lexeme lexbuf) }
 | '['                   { (Lexing.lexeme lexbuf) }
 | ']'                   { (Lexing.lexeme lexbuf) }
 | '{'                   { token lexbuf }
 | '}'                   { token lexbuf }
 | "active"              { ACTIVE }
 | "assert"              { ASSERT }
 | "atomic"              { ATOMIC }
 | "bit"                 { TYPE BIT }
 | "bool"                { TYPE BIT }
 | "break"               { BREAK }
 | "byte"                { TYPE BYTE }
 | "c_code"              { C_CODE }
 | "c_decl"              { C_DECL }
 | "c_expr"              { C_EXPR }
 | "c_state"             { C_STATE }
 | "c_track"             { C_TRACK }
 | "D_proctype"          { D_PROCTYPE }
 | "do"                  { DO }
 | "chan"                { TYPE CHAN }
 | "else"                { ELSE }
 | "empty"               { EMPTY }
 | "enabled"             { ENABLED }
 | "eval"                { EVAL }
 | "false"               { CONST 0 }
 | "fi"                  { FI }
 | "for"                 { FOR }
 | "full"                { FULL }
 | "goto"                { GOTO }
 | "hidden"              { HIDDEN }
 | "if"                  { IF }
 | "in"                  { IN }
 | "init"                { INIT }
 | "inline"              { INLINE }
 | "int"                 { TYPE INT }
 | "len"                 { LEN }
 | "local"               { ISLOCAL }
 | "ltl"                 { LTL }
 | "mtype"               { TYPE MTYPE }
 | "nempty"              { NEMPTY }
 | "never"               { NEVER }
 | "nfull"               { NFULL }
 | "notrace"             { NOTRACE }
 | "np_"                 { NONPROGRESS }
 | "od"                  { OD }
 | "of"                  { OF }
 | "pc_value"            { PC_VAL }
 | "pid"                 { TYPE SHORT }
 | "printf"              { PRINT }
 | "printm"              { PRINTM }
 | "priority"            { PRIORITY }
 | "proctype"            { PROCTYPE }
 | "provided"            { PROVIDED }
 | "run"                 { RUN }
 | "d_step"              { D_STEP }
 | "select"              { SELECT }
 | "short"               { TYPE SHORT }
 | "skip"                { CONST }
 | "timeout"             { TIMEOUT }
 | "trace"               { TRACE }
 | "true"                { CONST 1 }
 | "show"                { SHOW }
 | "typedef"             { TYPEDEF }
 | "unless"              { UNLESS }
 | "unsigned"            { TYPE UNSIGNED }
 | "xr"                  { XU XR }
 | "xs"                  { XU XS }
 | ['_' 'A'-'z']['_' 'A'-'z' '0'-'9']* { NAME (Lexing.lexeme lexbuf) }
 | ['0'-'9']+            { CONST (int_of_string (Lexing.lexeme lexbuf)) }
 | '"' [^ '"']* '"'      { STRING (string_chars (Lexing.lexeme lexbuf)) }
 | '#' ['_' 'A'-'z']['_' 'A'-'z' '0'-'9']*  { MACRO (pp_word (Lexing.lexeme lexbuf)) }
 | _ as c                { raise Unexpected_token (sprintf "Unrecognized char: %c" c) }
and comment = parse
 | "*/"                  { token lexbuf }
 | _                     { comment lexbuf }
 | eof                   { raise End_of_file }
