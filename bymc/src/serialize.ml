(* Save/restore important data structures,
   print a global state and parse it back.

   Igor Konnov, 2013
 *)

open Printf

open Accums
open Program

let print_global_state prog =
    let format_var v =
        if v#is_array
        then let vals =
            str_join "," (List.map (fun _ -> "%d") (range 0 v#nelems) )
        in sprintf "%s={%s}" v#qual_name vals
        else sprintf "%s=%%d" v#qual_name
    in
    let strs = List.map format_var (prog#get_instrumental @ prog#get_shared)
    in
    str_join "," strs

