open Printf;;

open Spin_ir;;
open Spin_ir_imp;;

module IntSet = Set.Make (struct
 type t = int
 let compare a b = a - b
end);;

class ['t] basic_block =
    object(self)
        val mutable seq: 't stmt list = []
        val mutable succ: 't basic_block list = []

        method set_seq s = seq <- s
        method get_seq = seq

        method set_succ s = succ <- s
        method get_succ = succ

        method get_exit_labs =
            match List.hd (List.rev seq) with
                | Goto i -> [i]
                | If is -> is
                | _ -> [] (* an exit block *)

        method get_lead_lab =
            match List.hd seq with
                | Label i -> i
                | _ -> raise (Failure "The basic block is corrupted, no leading label")

        method str =
            let exit_s = List.fold_left
                (fun a i -> sprintf "%s%d; " a i) "" self#get_exit_labs in
            (sprintf "Basic block %d [%s]:\n" self#get_lead_lab exit_s) ^
            (List.fold_left (fun a s -> sprintf "%s%s\n" a (stmt_s s)) "" seq)
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
        stmts
;;

(* split a list into a list of list each terminating with an element
   recognized by is_sep
 *)
let separate is_sep list_i =
    let rec sep_rec lst =
        match lst with
            | [] -> []
            | hd :: tl ->
                let res = sep_rec tl in
                match res with
                    | [] -> if is_sep hd then [[]; [hd]] else [[hd]]
                    | hdl :: tll ->
                        if is_sep hd
                        then [] :: (hd :: hdl) :: tll
                        else (hd :: hdl) :: tll
    in (* clean hanging empty sets *)
    List.filter (fun l -> l <> []) (sep_rec list_i)
;;

let basic_block_tbl_s bbs =
    Hashtbl.iter
        (fun i bb -> printf "\nBasic block %d:\n" i;
            List.iter (fun s -> printf "%s\n" (stmt_s s)) bb#get_seq)
        bbs
;;

let mk_cfg stmts =
    let seq_heads = collect_jump_targets stmts in
    let cleaned = List.filter (* remove non-referenced labels *)
        (fun s ->
            match s with
                | Label i -> IntSet.mem i seq_heads
                | _ -> true)
        stmts in
    let seq_list = separate
            (fun s ->
                match s with (* separate by jump targets *)
                    | Label i -> IntSet.mem i seq_heads
                    | _ -> false)
            (* add 0 in front to denote the entry label *)
            ((Label 0):: cleaned) in
    
    let blocks = Hashtbl.create (List.length seq_list) in
    (* create basic blocks *)
    List.iter
        (fun seq ->
            match seq with
            | (Label i) :: tl ->
                let b = new basic_block in
                b#set_seq seq; Hashtbl.add blocks i b
            | _ -> raise (Failure "Broken head: expected (Label i) :: tl"))
        seq_list;
    (* connect them *)
    Hashtbl.iter
        (fun i bb -> bb#set_succ
            (List.map (Hashtbl.find blocks) bb#get_exit_labs))
        blocks;
    (* return the hash table: heading_label: int -> basic_block *)
    blocks
