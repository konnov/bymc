(**
  A parser of extended Promela.

  @author Igor Konnov, 2012-2016
 *)

exception Syntax_err of string

(**
  Parse a Promela file and produce a program
  as well as a list of hints (pragmas).
 *)
val parse_promela:
    Options.options_t -> string -> string -> string
    -> (Program.program_t * (string * string) list)


(**
  Parse a Promela file from a channel and produce a program
  as well as a list of hints (pragmas).
 *)
val parse_promela_of_chan:
    Options.options_t -> in_channel -> string -> string
    -> (Program.program_t * (string * string) list)

(**
  Parse a single Promela expression.
 *)
val parse_expr:
    SpinIr.symb_tab -> string -> Spin.token SpinIr.expr

