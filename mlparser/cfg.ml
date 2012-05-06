open Spin_ir;;
open Spin_ir_imp;;

module IntSet = Set.Make (struct
 type t = int
 let compare a b = a - b
end);;

class ['t] basic_block =
    object
        val mutable seq: 't stmt list = []
        val mutable succ: 't basic_block list = []
    end
;;

let collect_jump_targets stmts =
    List.fold_left
        (fun targs stmt ->
            match stmt with
                | Goto i -> IntSet.add i targs
                | If is  -> List.fold_right IntSet.add is targs
                | _      -> targs
        )
        IntSet.empty
;;

(* split a list into a list of list each terminating with an element
   recognized by is_sep
 *)
let rec separate is_sep l =
    match l with
        | [] -> []
        | hd :: tl ->
            let res = separate is_sep tl in
                match res with
                    | [] -> [[hd]]
                    | hdl :: tll ->
                            if is_sep hd
                            then [hd] :: res
                            else (hd :: hdl) :: tll
;;

(*
let mk_cfg stmts =
    let seqs = Hashtbl.create 20 in
    let rec collect lab stmts =
        match stmts with
            | [] -> []
            | hd :: tl -> (* TODO: finish! *)
*)
