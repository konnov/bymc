open Printf;;

open Spin_ir;;
open Spin_ir_imp;;
open Debug;;

exception CfgError of string;;

module IntSet = Set.Make (struct
 type t = int
 let compare a b = a - b
end);;

class ['t] basic_block =
    object(self)
        val mutable seq: 't stmt list = []
        val mutable succ: 't basic_block list = []
        val mutable pred: 't basic_block list = []
        (* this flag can be used to traverse along basic blocks *)
        val mutable visit_flag = false

        method set_seq s = seq <- s
        method get_seq = seq

        method set_succ s = succ <- s
        method get_succ = succ

        method set_pred p = pred <- p
        method get_pred = pred

        method set_visit_flag f = visit_flag <- f
        method get_visit_flag = visit_flag

        method get_exit_labs =
            match List.hd (List.rev seq) with
                | Goto (_, i) -> [i]
                | If (_, is, _) -> is
                | _ -> [] (* an exit block *)

        method get_lead_lab =
            match List.hd seq with
                | Label (_, i) -> i
                | _ -> raise (CfgError "Corrupted basic block, no leading label")

        method str =
            let exit_s = List.fold_left
                (fun a i ->
                    sprintf "%s%s%d" a (if a <> "" then ", " else "") i) 
                "" self#get_exit_labs in
            (sprintf "Basic block %d [succs: %s]:\n" self#get_lead_lab exit_s) ^
            (List.fold_left (fun a s -> sprintf "%s%s\n" a (stmt_s s)) "" seq)
    end
;;

class ['t, 'attr] attr_basic_block a =
    object(self)
        inherit ['t] basic_block as super

        val mutable attr: 'attr = a

        method as_basic_block = (self :> ('t) basic_block)

        method set_attr a = attr <- a
        
        method get_attr = attr
    end
;;

class ['t] control_flow_graph i_entry i_blocks =
    object(self)
        val m_blocks: (int, 't basic_block) Hashtbl.t = i_blocks
        val m_entry: 't basic_block = i_entry

        method blocks = m_blocks
        method entry = m_entry
    end
;;

(* collect labels standing one next to each other *)
let merge_neighb_labels stmts =
    let neighb = Hashtbl.create 10
    in
    List.iter2
        (fun s1 s2 ->
            match s1, s2 with
            | Label (_, i), Label (_, j) ->
                if Hashtbl.mem neighb i
                (* add the neighbor of i *)
                then Hashtbl.add neighb j (Hashtbl.find neighb i)
                (* add i itself *)
                else Hashtbl.add neighb j i
            | _ -> ()
        )
        (List.rev (List.tl (List.rev stmts))) (List.tl stmts);
    let sub_lab i = if (Hashtbl.mem neighb i) then Hashtbl.find neighb i else i
    in
    List.map
        (fun s ->
            match s with
            | Goto (id, i) ->
                    Goto (id, sub_lab i)
            | If (id, targs, exit) ->
                    If (id, (List.map sub_lab targs), (sub_lab exit))
            | _ -> s
        ) stmts
;;

let collect_jump_targets stmts =
    List.fold_left
        (fun targs stmt ->
            match stmt with
                | Goto (_, i) -> IntSet.add i targs
                | If (_, is, _)  -> List.fold_right IntSet.add is targs
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
                    | [] ->
                        if is_sep hd then [[]; [hd]] else [[hd]]
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
    let stmts_r = merge_neighb_labels stmts in
    let seq_heads = collect_jump_targets stmts_r in
    let cleaned = List.filter (* remove hanging unreferenced labels *)
        (function
            | Label (_, i) -> IntSet.mem i seq_heads
            | _ -> true
        ) stmts_r in
    let seq_list = separate
            (fun s ->
                match s with (* separate by jump targets *)
                    | Label (_, i) -> IntSet.mem i seq_heads
                    | _ -> false)
            (* add 0 in front to denote the entry label *)
            (Label (-1, 0) :: cleaned) in
    let blocks = Hashtbl.create (List.length seq_list) in
    (* create basic blocks *)
    let mk_bb seq next_seq =
        let has_terminator =
            match (List.hd (List.rev seq)) with
            | Goto (_, _) -> true
            | If (_, _, _) -> true
            | _ -> false
        in
        let get_entry_lab = function
        | Label (_, i) :: _ -> i
        | _ -> raise (CfgError "Broken head: expected (Label i) :: tl")
        in
        let entry_lab = (get_entry_lab seq) in
        let body = if not has_terminator
        then seq @ [Goto (-1, (get_entry_lab next_seq))]
        else seq in
        let bb = new basic_block in
        bb#set_seq body;
        Hashtbl.add blocks entry_lab bb;
        bb
    in
    (*
    let entry = mk_bb (List.hd seq_list) in
    *)
    let bbs = List.map2 mk_bb
        seq_list ((List.tl seq_list) @ [[Label (-1, 0)]]) in
    (*
    List.iter (fun seq -> let _ = mk_bb seq in ()) (List.tl seq_list);
     *)
    let entry = List.hd bbs in
    (* set successors *)
    Hashtbl.iter
        (fun _ bb -> bb#set_succ
            (List.map (Hashtbl.find blocks) bb#get_exit_labs))
        blocks;
    (* set predecessors *)
    Hashtbl.iter
        (fun _ bb ->
            List.iter (fun s -> s#set_pred (bb :: s#get_pred)) bb#get_succ)
        blocks;
    (* return the hash table: heading_label: int -> basic_block *)
    new control_flow_graph entry blocks
;;

(* This is a very naive implementation. We do not expect it to be run
   on hundreds of basic blocks. If this happens, implement an algorithm
   from Muchnik
 *)
let find_dominator bbs =
    let all_labs =
        List.fold_left (fun set bb -> IntSet.add bb#get_lead_lab set)
            IntSet.empty bbs in
    let doms = List.fold_left
        (fun set bb ->
            List.fold_left
                (fun new_set succ -> IntSet.remove succ#get_lead_lab new_set)
                set bb#get_succ
        ) all_labs bbs
    in
    match IntSet.elements doms with
    | [one_lab] -> List.find (fun bb -> bb#get_lead_lab = one_lab) bbs
    | [] -> raise (CfgError "No dominators found for a set of basic blocks")
    | _ -> raise (CfgError "Several dominators for a set of basic blocks")
;;

type label = { node_num: int; low: int; on_stack: bool };;

(*
  A function to find strongly connected components by Tarjan's algorithm.
  We ignore singleton sets.

  Imperative code like in the book by Aho et al.
 *)
let comp_sccs first_bb =
    let labels = Hashtbl.create 10 in
    let set_lab b l = Hashtbl.replace labels b#get_lead_lab l in
    let get_lab b = Hashtbl.find labels b#get_lead_lab in
    let has_lab b = Hashtbl.mem labels b#get_lead_lab in
    let sccs = ref [] in
    let stack = ref [] in
    let counter = ref 0 in
    let next_num () =
        let n = !counter in
        counter := n + 1; n
    in
    let rec search b =
        let num = next_num () in
        set_lab b { node_num = num; low = num; on_stack = true };
        log DEBUG (sprintf " PUSH %d # %d!\n" b#get_lead_lab num);
        stack := b :: !stack;
        List.iter
            (fun w ->
                if not (has_lab w)
                then begin
                    let res = search w in
                    let lab_w, lab_b = get_lab w, get_lab b in
                    set_lab b { lab_b with low = (min lab_w.low lab_b.low) };
                    res
                end
                else begin
                    let lab_w, lab_b = get_lab w, get_lab b in
                    if (lab_w.node_num < lab_b.node_num) && lab_w.on_stack
                    then set_lab b
                        { lab_b with low = (min lab_w.low lab_b.low) }
                end
            ) b#get_succ;
        
        let lab_b = get_lab b in
        if lab_b.node_num = lab_b.low
        then begin
            log DEBUG (sprintf " UNWIND %d at %d!\n" num b#get_lead_lab);
            let hd, el, tl = Accums.list_cut
                (fun b -> (get_lab b).node_num = lab_b.node_num)
                !stack
            in
            if (hd <> []) then sccs := (List.rev (hd @ el)) :: !sccs;
            stack := tl;
            List.iter
                (fun b ->
                    log DEBUG (sprintf " POPPED: %d\n" b#get_lead_lab);
                    let l = get_lab b in
                    set_lab b { l with on_stack = false }
                ) (hd @ el)
        end
    in
    let fn = next_num () in
    set_lab first_bb { node_num = fn; low = fn; on_stack = true };
    search first_bb;
    !sccs
;;
