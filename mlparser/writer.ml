(* Write Promela code from its intermediate representation *)

let write_stmt cout indent s =
    ()
;;
  
let write_proc cout indent p =
    ()
;;

let write_unit cout indent u =
    match u with
    | Stmt s -> write_stmt cout indent s
    | Proc p -> write_proc cout indent p
    | _ -> ()
;;
