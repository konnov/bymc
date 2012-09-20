(* Spin lexical analyzer is context-dependent in the sense it returns different
   tokens, remaining in different grammar subtrees. Thus, we have to switch
   the lexer into different modes. The original Spin lexer has tricky code for
   this.

   This is a boilerplate code to provide lexer with the feedback from the
   parser. I do not see any way in yacc/lex different from global references.
   Please do use this module as less as possible.

   Igor Konnov 2012
 *)

type lexer_mode = LexerNormal | LexerLtl;;

val current_lexer_mode: lexer_mode ref;;

val set_lexer_normal: unit -> unit;;
val set_lexer_ltl: unit -> unit;;

val is_lexer_normal: unit -> bool;;
val is_lexer_ltl: unit -> bool;;

