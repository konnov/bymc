(* Executing a path symbolically and collecting the constraints along it
 *
 * Igor Konnov, 2013
 *)

open Cfg
open Spin
open SpinIr

type var_cons_tbl = (string, int) Hashtbl.t

let push_var tbl var_name expr =
    if not (Hashtbl.mem tbl var_name)
    then Hashtbl.add var_name 0
    else let max_ver = Hashtbl.find tbl var_name in
        Hashtbl.replace var_name (1 + max_ver)


let var_versions tbl var_name =
    if not (Hashtbl.mem tbl var_name)
    then begin
        Hashtbl.add var_name 0;
        0
    end
    else Hashtbl.find tbl var_name


let exec_path (path: token basic_block list) =
    let tbl = Hashtbl.create 10 in
    let sub_ver = function
    | Var v -> Var v (* replace with a var version... *)
    in
    let exec_stmt = function
    | Expr (_, BinEx (ASGN, lhs, rhs)) as s -> s
    | _ as s -> s
    in
    ()
