(*
 * Substitute parameter values and produce standard Promela code.
 *)

open Map
module StringMap = Map.Make (String)

open SpinIr

let concretize_stmt param_assignments = function
    | _ as s -> s
;;

let concretize_proc param_assignments p =
    p
;;

let concretize_unit param_assignments = function
    | None -> None
    | Ltl (_, _) as e -> e
    | Stmt s -> Stmt (concretize_stmt param_assignments s)
    | Proc p -> Proc (concretize_proc param_assignments p)
;;

let do_substitution (param_assignments: int StringMap.t)
        (units: 't prog_unit list) : ('t prog_unit list) =
    List.map (concretize_unit param_assignments) units
;;
