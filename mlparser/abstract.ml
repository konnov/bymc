open Parse;;
open Spin_ir;;

type var_role = Pc | Shared | Local | Next;;

let var_role_s r =
    match r with
    | Pc -> "pc"
    | Shared -> "shared"
    | Local -> "local"
    | Next -> "next"
;;

let identify_var_roles units =
    let tbl = Hashtbl.create 10 in
    let assign_role is_local name =
        if not is_local
        then Shared
        else if name = "pc"
        then Pc
        else if (String.sub name 0 (min 5 (String.length name))) = "next_"
        then Next
        else Local
    in
    let process_stmt is_local s =
        match s with
            | Decl (v, e) ->
                if not v#is_symbolic
                then Hashtbl.add tbl v (assign_role is_local v#get_name)
            | _ -> ()
    in
    List.iter
        (fun u ->
            match u with
            | Stmt s -> process_stmt false s
            | Proc p -> List.iter (process_stmt true) p#get_stmts
            | _ -> ()
        )
        units;
    tbl

