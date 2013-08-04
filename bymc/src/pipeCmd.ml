(*
 * see pipeCmd.mli
 *)

exception Comm_error of string

type cmd_stat = { status: int }

let create prog args = { status = 0 }

let destroy cs = true

let readline cs = ""

let writeline cs str = ()

