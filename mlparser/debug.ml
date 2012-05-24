(* simple logging/debugging facility *)

type verbosity = QUIET | ERROR | WARN | INFO | DEBUG;;

let current_verbosity_level = ref INFO;; (* extremely long on purpose *)

let verbosity_s = function
    | QUIET -> ""
    | ERROR -> "ERR  "
    | WARN -> "WARN   "
    | INFO -> " "
    | DEBUG -> " *** "
;;

let may_log level =
    let to_num = function
        | QUIET -> 0
        | ERROR -> 1
        | WARN -> 2
        | INFO -> 3
        | DEBUG -> 4
    in
    (to_num level) <= (to_num !current_verbosity_level)
;;

let log level message =
    if may_log level
    then Printf.printf "%s %s\n" (verbosity_s level) message
;;

