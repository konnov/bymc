open Printf

open Accums
open SpinIr
open SpinIrImp
open Debug

exception CfgError of string

module IntSet = Set.Make (struct
 type t = int
 let compare a b = a - b
end)

class ['t] basic_block =
    object(self)
        val mutable seq: 't stmt list = []
        val mutable succ: 't basic_block list = []
        val mutable pred: 't basic_block list = []
        (* phi functions incoming into the block (see SSA) *)
        val mutable phis: 't expr list = []
        (* this flag can be used to traverse along basic blocks *)
        val mutable visit_flag = false

        method set_seq s = seq <- s
        method get_seq = seq

        method set_succ s = succ <- s
        method get_succ = succ
        method succ_labs = List.map (fun bb -> bb#label) succ

        method set_pred p = pred <- p
        method get_pred = pred
        method pred_labs = List.map (fun bb -> bb#label) pred
        method find_pred_idx lab =
            let pairs = List.combine (range 0 (List.length pred)) pred in
            let idx, _ = List.find (fun (i, bb) -> bb#label = lab) pairs in
            idx

        method set_phis s = phis <- s
        method get_phis = phis

        method set_visit_flag f = visit_flag <- f
        method get_visit_flag = visit_flag

        method get_exit_labs =
            match List.hd (List.rev seq) with
                | Goto (_, i) -> [i]
                | If (_, is, _) -> is
                | _ -> [] (* an exit block *)

        (* deprecated, use label *)
        method get_lead_lab =
            match List.hd seq with
                | Label (_, i) -> i
                | _ -> raise (CfgError "Corrupted basic block, no leading label")

        method label = self#get_lead_lab

        method str =
            let exit_s = List.fold_left
                (fun a i ->
                    sprintf "%s%s%d" a (if a <> "" then ", " else "") i) 
                "" self#get_exit_labs in
            (sprintf "Basic block %d [succs: %s]:\n" self#get_lead_lab exit_s) ^
            (List.fold_left (fun a s -> sprintf "%s%s\n" a (stmt_s s)) "" seq)
    end


let bb_lab bb = bb#label

class ['t, 'attr] attr_basic_block a =
    object(self)
        inherit ['t] basic_block as super

        val mutable attr: 'attr = a

        method as_basic_block = (self :> ('t) basic_block)

        method set_attr a = attr <- a
        
        method get_attr = attr
    end


class ['t] control_flow_graph i_entry i_blocks =
    object(self)
        val m_blocks: (int, 't basic_block) Hashtbl.t = i_blocks
        val m_entry: 't basic_block = i_entry

        method blocks = m_blocks
        method block_list = Accums.hashtbl_vals m_blocks
        method block_labs = Accums.hashtbl_keys m_blocks
        method entry = m_entry

        method find lab = Hashtbl.find m_blocks lab
    end


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
            (Label (fresh_id (), 0) :: cleaned) in
    let blocks = Hashtbl.create (List.length seq_list) in
    (* create basic blocks *)
    let exit_label = 999999 in
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
        let body =
            if not has_terminator && (get_entry_lab next_seq) <> exit_label
        then seq @ [Goto (fresh_id (), (get_entry_lab next_seq))]
        else seq in
        let bb = new basic_block in
        bb#set_seq body;
        Hashtbl.add blocks entry_lab bb;
        bb
    in
    let bbs = List.map2 mk_bb
        seq_list ((List.tl seq_list) @ [[Label (fresh_id (), exit_label)]]) in
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


type label = { node_num: int; low: int; on_stack: bool }

(*
  A function to find strongly connected components by Tarjan's algorithm.
  Singleton sets are ignored.

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


(*
Compute dominators for a node. The algorithm is copied as it is.

S. Muchnik. Advanced Compiler Design and Implementation, p. 182, Fig. 7.14.
*)
let comp_doms cfg =
    let domin = Hashtbl.create (Hashtbl.length cfg#blocks) in
    let all = List.fold_left
        (fun s bb -> IntSet.add bb#label s) IntSet.empty cfg#block_list in
    let all_but_0 = IntSet.remove 0 all in
    let init_domin n = if n <> 0 then all else IntSet.singleton 0 in
    IntSet.iter (fun n -> Hashtbl.add domin n (init_domin n)) all;
    let change = ref true in
    while !change do
        change := false;
        let update n =
            let t = List.fold_left
                (fun s bb_lab ->
                    IntSet.inter (Hashtbl.find domin bb_lab) s
                ) all (cfg#find n)#pred_labs in
            let n_doms = IntSet.union t (IntSet.singleton n) in
            if n_doms <> (Hashtbl.find domin n) then
            begin
                change := true;
                Hashtbl.replace domin n n_doms
            end
        in
        IntSet.iter update all_but_0
    done;
    domin


(*
Compute immediate dominators for a node.
Minor changes made to write it in OCaml.

S. Muchnik. Advanced Compiler Design and Implementation, p. 182, Fig. 7.15.
*)
let comp_idoms cfg =
    let all = List.fold_left
        (fun s bb -> IntSet.add bb#label s) IntSet.empty cfg#block_list in
    let all_but_0 = IntSet.remove 0 all in
    let domin = comp_doms cfg in
    let tmp = Hashtbl.create (Hashtbl.length domin) in
    let init_tmp n =
        Hashtbl.add tmp n (IntSet.remove n (Hashtbl.find domin n)) in
    List.iter init_tmp cfg#block_labs;
    let update n s t =
        if IntSet.mem t (Hashtbl.find tmp s)
        then Hashtbl.replace tmp n (IntSet.remove t (Hashtbl.find tmp n)) in
    let inner2 n s =
        IntSet.iter (update n s) (IntSet.remove s (Hashtbl.find tmp n)) in
    let inner n =
        IntSet.iter (inner2 n) (Hashtbl.find tmp n) in
    IntSet.iter inner all_but_0;
    let idom = Hashtbl.create (Hashtbl.length cfg#blocks) in
    let add_idom n idom_set =
        assert ((IntSet.cardinal idom_set) <= 1);
        let dom = if n = 0
            then -1
            else (List.hd (IntSet.elements idom_set)) in
        Hashtbl.add idom n dom in
    Hashtbl.iter add_idom tmp;
    idom


let comp_idom_tree idoms =
    let children = Hashtbl.create (Hashtbl.length idoms) in
    Hashtbl.iter (fun _ idom -> Hashtbl.add children idom []) idoms;
    Hashtbl.iter (fun n _ -> Hashtbl.replace children n []) idoms;
    let add n idom =
        Hashtbl.replace children idom (n :: (Hashtbl.find children idom)) in
    Hashtbl.iter add idoms;
    children


let print_detailed_cfg title cfg =
    printf "\n%s\n" title;
    let idom = comp_idoms cfg in
    let idom_tree = comp_idom_tree idom in
    let print_blk i =
        let bb = cfg#find i in
        let bb_s blk = string_of_int blk#label in
        let succ_s = String.concat ", " (List.map bb_s bb#get_succ) in
        let pred_s = String.concat ", " (List.map bb_s bb#get_pred) in
        printf "\nBasic block %d [idom = %d, succ = %s, pred = %s]:\n"
            i (Hashtbl.find idom i) succ_s pred_s;
        List.iter (fun s -> printf "  %s\n" (stmt_s s)) bb#get_seq
    in
    let rec bfs_list node =
        let children = Hashtbl.find idom_tree node in
        node :: (List.concat (List.map bfs_list children))
    in
    List.iter print_blk (bfs_list 0)


let write_dot (out_name: string) (cfg: 't control_flow_graph) =
    let fo = open_out out_name in
    let rec break s tw = 
        (* I am sure it can be done with Format if a day wasted *)
        if String.length s < tw
        then s
        else
            let p = try String.rindex_from s (tw - 1) ' ' with Not_found -> tw in
            let bpos = (if p = 0 then tw else p) in
            (String.sub s 0 bpos) ^ "\\n    "
                ^ (break (String.sub s bpos ((String.length s) - bpos)) tw)
    in
    let rec write_bb bb =
        let label = String.concat "\n" (List.map stmt_s bb#get_seq) in
        let elabel = String.escaped label in
        fprintf fo "  bb%d [label = \"%s\\n\"];\n" bb#label (break elabel 40)
    in
    let rec write_bb_succ bb =
        let connect_succ succ_lab =
            fprintf fo "  bb%d -> bb%d;\n" bb#label succ_lab in
        List.iter connect_succ bb#succ_labs
    in
    fprintf fo "digraph cfg {\n";
    fprintf fo "  size=\"11.5,8.0\";\n";
    fprintf fo "  rotate=90;\n";
    fprintf fo "  node [shape=box];\n";
    List.iter write_bb cfg#block_list;
    List.iter write_bb_succ cfg#block_list;
    fprintf fo "}\n";
    close_out fo


(*
 Enumerate all possible finite paths in an acyclic graph.
 We use a naive DFS algorithm, it works only on small graphs!
 *)
let enum_paths (cfg: 't control_flow_graph)
        (path_fun: 't basic_block list -> unit): int =
    (*
    let sccs = comp_sccs cfg#entry in
    if sccs <> [] then raise (CfgError "CFG has a cycle!");
    *)
    
    let rec dfs path bb =
        if bb#get_visit_flag
        then raise (CfgError
            (sprintf "Graph is cyclic: %d -> .. -> %d" bb#label bb#label))
        else bb#set_visit_flag true;
        let new_path = bb :: path in
        let num = if bb#get_succ = [] (* the final state is reached *)
        then begin
            path_fun (List.rev new_path);
            1 (* one path enumerated *)
        end else List.fold_left (+) 0
            (List.map (dfs new_path) bb#get_succ) (* many paths *)
        in
        bb#set_visit_flag false;
        num
    in
    let num_paths = dfs [] cfg#entry in
    List.iter (fun bb -> bb#set_visit_flag false) cfg#block_list;
    num_paths

