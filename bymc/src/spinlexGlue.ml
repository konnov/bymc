(* see spinlexGlue.mli *)

type lexer_mode = LexerNormal | LexerLtl;;

let current_lexer_mode = ref LexerNormal;;

let set_lexer_normal unit = current_lexer_mode := LexerNormal;;
let set_lexer_ltl unit = current_lexer_mode := LexerLtl;;

let is_lexer_normal unit = !current_lexer_mode = LexerNormal;;
let is_lexer_ltl unit = !current_lexer_mode = LexerLtl;;

