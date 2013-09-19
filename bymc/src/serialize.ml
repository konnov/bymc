(* Save/restore important data structures,
   print a global state and parse it back.

   Igor Konnov, 2013
 *)

open Printf

open Accums
open Program
open Spin
open SpinIr
open Str

let global_state_fmt prog =
    let format_var v =
        let tp = Program.get_type prog v in
        if tp#is_array
        then let vals =
            str_join "," (List.map (fun _ -> "%d") (range 0 tp#nelems) )
        in sprintf "%s={%s}" v#qual_name vals
        else sprintf "%s=%%d" v#qual_name
    in
    let ref_var lst v =
        let add_elem_ref es i =
            (BinEx(ARR_ACCESS, Var v, Const i) :: es) in
        let tp = Program.get_type prog v in
        if tp#is_array
        then List.fold_left add_elem_ref lst (range 0 tp#nelems)
        else (Var v) :: lst
    in
    let vars = (Program.get_instrumental prog) @ (Program.get_shared prog) in
    let strs = List.map format_var vars in
    let exprs = List.rev (List.fold_left ref_var [] vars) in
    (sprintf "S{%s}" (str_join "," strs), exprs)

let global_state_re fmt =
    let re_s = Str.global_replace (Str.regexp_string "%d") "\\([0-9]+\\)" fmt in
    Str.regexp re_s

let parse_global_state prog text =
    let fmt, es = global_state_fmt prog in
    let re = global_state_re fmt in
    let bind group expr =
        let value = int_of_string (Str.matched_group (1 + group) text) in
        BinEx(EQ, expr, Const value)
    in
    if Str.string_match re text 0
    then List.map2 bind (range 0 (List.length es)) es
    else []

