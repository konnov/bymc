(* Single static assignment form.
 *
 * This module is written in Dubrovnik next to Adriatic sea.
 * So it may have more bugs than the other modules!
 *
 * Igor Konnov, 2012-2013.
 *)

open Printf

open Accums
open Analysis
open Cfg
open Debug
open Spin
open SpinIr
open SpinIrImp


exception Var_not_found of string

let comp_dom_frontiers cfg =
    let df = Hashtbl.create (Hashtbl.length cfg#blocks) in
    let idom_tbl = comp_idoms cfg in
    let idom_tree = comp_idom_tree idom_tbl in
    let visit_node n =
        let visit_y s df_n =
            if n <> (Hashtbl.find idom_tbl s)
            then IntSet.add s df_n
            else df_n in
        let df_n = List.fold_right visit_y (cfg#find n)#succ_labs IntSet.empty 
        in
        let propagate_up df_n z =
            IntSet.fold visit_y (Hashtbl.find df z) df_n in
        let children = Hashtbl.find idom_tree n in
        let df_n = List.fold_left propagate_up df_n children in
        Hashtbl.add df n df_n
    in
    let rec bottom_up node =
        try
            let children = Hashtbl.find idom_tree node in
            List.iter bottom_up children;
            visit_node node
        with Not_found ->
            raise (Failure (sprintf "idom children of %d not found" node))
    in
    bottom_up 0;
    df


(* Ron Cytron et al. Efficiently Computing Static Single Assignment Form and
   the Control Dependence Graph, ACM Transactions on PLS, Vol. 13, No. 4, 1991,
   pp. 451-490.

   Figure 11.
 *)
let place_phi (vars: var list) (cfg: 't control_flow_graph) =
    let df = comp_dom_frontiers cfg in
    let iter_cnt = ref 0 in
    let has_already = Hashtbl.create (Hashtbl.length cfg#blocks) in
    let work = Hashtbl.create (Hashtbl.length cfg#blocks) in
    let init_node n =
        Hashtbl.add has_already n 0; Hashtbl.add work n 0 in
    List.iter init_node cfg#block_labs;

    let for_var v =
        let does_stmt_uses_var = function
            | Expr (_, BinEx (ASGN, Var ov, _)) ->
                    ov#qual_name = v#qual_name
            | Expr (_, BinEx (ASGN, BinEx (ARR_ACCESS, Var ov, _), _)) ->
                    ov#qual_name = v#qual_name
            | Havoc (_, ov) ->
                    ov#qual_name = v#qual_name
            | _ -> false in
        let does_blk_uses_var bb =
            List.exists does_stmt_uses_var bb#get_seq in
        let blks_using_v =
            List.map bb_lab (List.filter does_blk_uses_var cfg#block_list) in
        iter_cnt := !iter_cnt + 1;
        List.iter (fun bb -> Hashtbl.replace work bb !iter_cnt) blks_using_v;
        let work_list = ref blks_using_v in
        let one_step x =
            let do_y y = 
                if (Hashtbl.find has_already y) < !iter_cnt
                then begin
                    let bb = cfg#find y in
                    let num_preds = (List.length bb#get_pred) in
                    let phi = Expr (fresh_id (),
                                    Phi (v, Accums.n_copies num_preds v))
                    in
                    let seq = bb#get_seq in
                    bb#set_seq ((List.hd seq) :: phi :: (List.tl seq));
                    Hashtbl.replace has_already y !iter_cnt;
                    if (Hashtbl.find work y) < !iter_cnt
                    then begin
                        Hashtbl.replace work y !iter_cnt;
                        work_list := y :: !work_list
                    end
                end
            in
            IntSet.iter do_y (Hashtbl.find df x)
        in
        let rec many_steps () =
            match !work_list with
            | hd :: tl -> work_list := tl; one_step hd; many_steps ()
            | [] -> ()
        in
        work_list := blks_using_v;
        many_steps ()
    in
    List.iter for_var vars;
    cfg


let map_rvalues map_fun ex =
    let rec sub = function
    | Var v -> map_fun v
    | UnEx (t, l) ->
            UnEx (t, sub l)
    | BinEx (ASGN, BinEx (ARR_ACCESS, arr, idx), r) ->
            BinEx (ASGN, BinEx (ARR_ACCESS, arr, sub idx), sub r)
    | BinEx (ASGN, l, r) ->
            BinEx (ASGN, l, sub r)
    | BinEx (t, l, r) ->
            BinEx (t, sub l, sub r)
    | _ as e -> e
    in
    sub ex


(*
 It appears that the Cytron's algorithm can produce redundant phi functions like
 x_2 = phi(x_1, x_1, x_1). Here we remove them.
 *)
let optimize_ssa cfg =
    let sub_tbl = Hashtbl.create 10 in
    let sub_var v =
        if Hashtbl.mem sub_tbl (v#id, v#mark)
        then Var (Hashtbl.find sub_tbl (v#id, v#mark))
        else Var v
    in
    let map_s s = map_expr_in_lir_stmt (map_vars sub_var) s in
    let changed = ref true in
    let reduce_phi bb =
        let on_stmt = function
            | Expr (id, Phi (lhs, rhs)) as s ->
                    let fst = List.hd rhs in
                    if List.for_all (fun o -> o#mark = fst#mark) rhs
                    then begin
                        Hashtbl.add sub_tbl (fst#id, fst#mark) lhs;
                        changed := true;
                        Skip id 
                    end else s
            | _ as s -> s
        in
        bb#set_seq (List.map on_stmt bb#get_seq);
    in
    while !changed do
        changed := false;
        List.iter reduce_phi cfg#block_list;
        List.iter
            (fun bb -> bb#set_seq (List.map map_s bb#get_seq)) cfg#block_list
    done;
    cfg


let add_mark_to_name new_sym_tab new_type_tab v =
    let copy v new_name =
        try (new_sym_tab#lookup new_name)#as_var
        with Symbol_not_found _ ->
            let newv = v#fresh_copy new_name in
            new_sym_tab#add_symb newv#get_name (newv :> symb);
            new_type_tab#set_type newv (new_type_tab#get_type v);
            newv
    in
    if v#is_symbolic
    then Var v (* don't touch it *)
    else if v#mark = 0
    then Var (copy v (sprintf "%s_IN" v#get_name))
    else if v#mark = max_int
    then Var (copy v (sprintf "%s_OUT" v#get_name))
    else Var (copy v (sprintf "%s_Y%d" v#get_name v#mark))


let get_var_copies var seq =
    let add_if l v = if v#id = var#id then v :: l else l in
    let add_copy l = function
        | Decl (_, v, _) ->
                add_if l v 
        | Expr (_, Phi (v, _)) ->
                add_if l v 
        | Expr (_, BinEx (ASGN, Var v, _)) ->
                add_if l v 
        | Expr (_, BinEx (ASGN, BinEx (ARR_ACCESS, Var v, _), _)) ->
                add_if l v 
        | Havoc (_, v) ->
                add_if l v 
        | _ -> l
    in
    List.fold_left add_copy [] seq


module IGraph = Graph.Pack.Digraph
module IGraphColoring = Graph.Coloring.Make(IGraph)
module IGraphOper = Graph.Oper.I(IGraph)

module VarGraph = Graph.Imperative.Digraph.Concrete(
    struct
        type t = var
        let compare lhs rhs =
            if lhs#id = rhs#id
            then lhs#mark - rhs#mark
            else lhs#id - rhs#id

        let hash v = v#id * v#mark

        let equal lhs rhs = (lhs#id = rhs#id && lhs#mark = rhs#mark)
    end
)    

module VarOper = Graph.Oper.I(VarGraph)
module VarColoring = Graph.Coloring.Make(VarGraph)


let print_dot filename var_graph =
    let ig = IGraph.create () in
    let addv v = IGraph.add_vertex ig (IGraph.V.create v#mark) in
    VarGraph.iter_vertex addv var_graph;
    let adde v w =
        IGraph.add_edge ig
            (IGraph.find_vertex ig v#mark) (IGraph.find_vertex ig w#mark)
    in
    (* FIXME: inefficient due to find_vertex *)
    VarGraph.iter_edges adde var_graph;
    IGraph.dot_output ig filename


(* for every basic block, find the starting indices of the variables,
   i.e., such indices that have not been used in immediate dominators.
 *)
let reduce_indices cfg var =
    let bcfg = cfg#as_block_graph in
    (* we need to track dependencies along paths *)
    ignore (BlockGO.add_transitive_closure ~reflexive:false bcfg);

    let get_bb_copies bb = get_var_copies var bb#seq in
    let depg = VarGraph.create () in
    let add_vertex var = VarGraph.add_vertex depg var in
    BlockG.iter_vertex (fun bb -> List.iter add_vertex (get_bb_copies bb)) bcfg;

    (* add dependencies *)
    let add_dep v1 v2 =
        if v1#mark <> v2#mark
        then VarGraph.add_edge depg v1 v2
    in
    let add_bb_deps bb =
        let copies = get_bb_copies bb in
        (* all copies are dependent in the block *)
        List.iter (fun v -> List.iter (add_dep v) copies) copies;
        let add_succ succ =
            let scopies = get_bb_copies succ in
            List.iter (fun v -> List.iter (add_dep v) scopies) copies
        in
        List.iter add_succ (BlockG.succ bcfg bb)
    in
    BlockG.iter_vertex add_bb_deps bcfg;

    (* all assignment along one path depend on each other *)
    ignore (VarOper.add_transitive_closure ~reflexive:false depg);
    (* remove self-loops that can be introduced by transitive closure *)
    VarGraph.iter_vertex (fun v -> VarGraph.remove_edge depg v v) depg;
    print_dot (sprintf "deps-%s.dot" var#get_name) depg;

    (* NOTE: coloring works only on undirected graphs,
       so we have to add the mirror *)
    let depg = VarOper.union depg (VarOper.mirror depg) in

    (* try to find minimal coloring via binary search *)
    let ecoloring = VarColoring.H.create 1 in
    let rec find_min_colors left right =
        let k = (left + right) / 2 in
        printf "%s: left=%d, right=%d, k=%d\n" var#get_name left right k;
        if left > right
        then (0, ecoloring)
        else let found, h =
            try true, VarColoring.coloring depg k
            with _ -> false, ecoloring
        in
        printf "found=%b\n" found;
        if found 
        then if left = right
            then (k, h)
            else
            let nk, nh = find_min_colors left k in
                if nk <> 0
                then (nk, nh)
                else (0, ecoloring)
        else find_min_colors (k + 1) right
    in
    let max_colors = VarGraph.nb_vertex depg in
    let ncolors, coloring = find_min_colors 1 max_colors in
    assert (max_colors = 0 || ncolors <> 0);
    (* find new marks. NOTE: we do not replace colors in place, as this
       might corrupt the vertex iterator. *)
    let fold v l =
        if v#mark <> 0 && v#mark <> Pervasives.max_int
        then (v, (VarColoring.H.find coloring v)) :: l
        else (v, v#mark) :: l
    in
    let new_marks = VarGraph.fold_vertex fold depg [] in
    List.iter (fun (v, c) -> v#set_mark c) new_marks;
    print_dot (sprintf "deps-%s-marked.dot" var#get_name) depg


(* Ron Cytron et al. Efficiently Computing Static Single Assignment Form and
   the Control Dependence Graph, ACM Transactions on PLS, Vol. 13, No. 4, 1991,
   pp. 451-490.

   Figure 12.

   NOTE: instead of renaming variables directly,
   we keep the new version number in var#mark.
 *)
let mk_ssa_cytron tolerate_undeclared_vars extern_vars intern_vars cfg =
    let vars = extern_vars @ intern_vars in
    if may_log DEBUG then print_detailed_cfg "CFG before SSA" cfg;
    let cfg = place_phi vars cfg in
    if may_log DEBUG then print_detailed_cfg "CFG after place_phi" cfg;
    let idom_tbl = comp_idoms cfg in
    let idom_tree = comp_idom_tree idom_tbl in

    let counters = Hashtbl.create (List.length vars) in
    let stacks = Hashtbl.create (List.length vars) in
    let nm v = v#id in
    let s_push v =
        try Hashtbl.replace stacks (nm v) (v :: (Hashtbl.find stacks (nm v)))
        with Not_found ->
            raise (Failure (sprintf "No stack for %s#%d" v#qual_name (nm v)))
    in
    let s_pop v = 
        try Hashtbl.replace stacks (nm v) (List.tl (Hashtbl.find stacks (nm v)))
        with Not_found ->
            raise (Failure (sprintf "No stack for %s#%d" v#qual_name v#id))
    in
    let intro_var v =
        let i =
            try Hashtbl.find counters (nm v)
            with Not_found ->
                raise (Var_not_found ("Var not found: " ^ v#qual_name))
        in
        let new_v = v#copy v#get_name in
        new_v#set_mark i;
        (* let new_v = v#copy (sprintf "%s_Y%d" v#get_name i) in *)
        s_push new_v;
        Hashtbl.replace counters (nm v) (i + 1);
        new_v
    in
    let s_top v =
        let stack =
            try Hashtbl.find stacks (nm v)
            with Not_found ->
                raise (Var_not_found ("No stack for " ^ v#qual_name))
        in
        if stack <> []
        then List.hd stack
        else if tolerate_undeclared_vars
        then intro_var v
        else raise (Failure (sprintf "%s: use before declaration?" v#qual_name))
    in
    let add_stack ?add_input:(add=false) v =
        Hashtbl.add stacks (nm v) [];
        if add then ignore (intro_var v) 
    in
    let add_counter base v = Hashtbl.add counters (nm v) base in
    (* initialize local variables: start with 1 as 0 is reserved for input *)
    List.iter (add_counter 1) intern_vars;
    List.iter add_stack intern_vars;
    (* global vars are different,
       each global variable x has a version x_0 referring
       to the variable on the input
     *)
    List.iter (add_counter 0) extern_vars;
    List.iter (add_stack ~add_input:true) extern_vars;

    let sub_var v =
        if v#is_symbolic
        (* do not touch symbolic variables, they are parameters! *)
        then v                (* TODO: what about atomic propositions? *)
        else s_top v
    in
    let sub_var_as_var e v =
        try Var (sub_var v)
        with Var_not_found m ->
            raise (Var_not_found (m ^ " in " ^ (expr_s e)))
    in
    let rec search x =
        let bb = cfg#find x in
        let bb_old_seq = bb#get_seq in
        let replace_rhs = function
            | Decl (id, v, e) ->
                    Decl (id, v, map_rvalues (sub_var_as_var e) e)
            | Expr (id, e) ->
                    Expr (id, map_rvalues (sub_var_as_var e) e)
            | Assume (id, e) ->
                    Assume (id, map_rvalues (sub_var_as_var e) e)
            | Assert (id, e) ->
                    Assert (id, map_rvalues (sub_var_as_var e) e)
            | _ as s -> s
        in
        let replace_lhs = function
            | Decl (id, v, e) -> Decl (id, (intro_var v), e)
            | Expr (id, BinEx (ASGN, Var v, rhs)) ->
                    Expr (id, BinEx (ASGN, Var (intro_var v), rhs))
            | Expr (id, (BinEx (ASGN, BinEx (ARR_ACCESS, Var v, idx), rhs) as e)) ->
                    (* A_i <- Update(A_j, k, e) *)
                    let old_arr =
                        try Var (sub_var v)
                        with Var_not_found m ->
                            raise (Var_not_found (m ^ " in " ^ (expr_s e)))
                    in
                    let upd = BinEx (ARR_UPDATE,
                        BinEx (ARR_ACCESS, old_arr, idx), rhs) in
                    Expr (id, BinEx (ASGN, Var (intro_var v), upd))
            | Expr (id, Phi (v, rhs)) ->
                    Expr (id, Phi (intro_var v, rhs))
            | Havoc (id, v) ->
                    (* just introduce a fresh one *)
                    let _ = intro_var v in
                    Skip id
            | _ as s -> s
        in
        let on_stmt lst s = (replace_lhs (replace_rhs s)) :: lst in
        bb#set_seq (List.rev (List.fold_left on_stmt [] bb#get_seq));
        (* put the variables in the successors *)
        let sub_phi_arg y =
            let succ_bb = cfg#find y in
            let j = Accums.list_find_pos x succ_bb#pred_labs in
            let on_phi = function
            | Expr (id, Phi (v, rhs)) ->
                let (before, e, after) = Accums.list_nth_slice rhs j in
                let new_e =
                    try sub_var e
                    with Var_not_found s ->
                        let m =
                            (sprintf "sub_phi_arg(x = %d, y = %d): %s" x y s) in
                        raise (Var_not_found m)
                in
                Expr (id, Phi (v, before @ (new_e :: after)))
            | _ as s -> s
            in
            succ_bb#set_seq (List.map on_phi succ_bb#get_seq)
        in
        List.iter sub_phi_arg bb#succ_labs;
        (* visit children in the dominator tree *)
        List.iter search (Hashtbl.find idom_tree x);
        (* our extension: if we are at the exit block,
           then add the output assignment for each shared variable x *)
        if bb#get_succ = []
        then
            (* declare the variables on the top of the stack
               to be output variables *)
            let mark_out v = (s_top v)#set_mark max_int in
            List.iter mark_out extern_vars;
        (* pop the stack for each assignment *)
        let pop_stmt = function
            | Decl (_, v, _) -> s_pop v
            | Expr (_, Phi (v, _)) -> s_pop v
            | Expr (_, BinEx (ASGN, Var v, _)) -> s_pop v
            | Expr (_, BinEx (ASGN, BinEx (ARR_ACCESS, Var v, _), _)) ->
                    s_pop v
            | Havoc (_, v) -> s_pop v
            | _ -> ()
        in
        List.iter pop_stmt bb_old_seq
    in
    search 0


(* (in-place) transformation of CFG to SSA.  *)
let mk_ssa tolerate_undeclared_vars extern_vars intern_vars
        new_sym_tab new_type_tab cfg =
    mk_ssa_cytron tolerate_undeclared_vars extern_vars intern_vars cfg;
    let rename_block bb =
        let map_s s =
            map_expr_in_lir_stmt
                (map_vars (add_mark_to_name new_sym_tab new_type_tab)) s in
        let ns = List.map map_s bb#get_seq in
        bb#set_seq ns
    in
    List.iter (reduce_indices cfg) intern_vars;
    List.iter (reduce_indices cfg) extern_vars;
    ignore (optimize_ssa cfg); (* optimize it after all *)
    List.iter rename_block cfg#block_list;
    cfg


(* move explicit statements x_1 = phi(x_2, x_3) to basic blocks (see bddPass) *)
let move_phis_to_blocks cfg =
    let move_in_bb bb =
        let on_stmt lst = function
        | Expr (_, Phi (lhs, rhs)) ->
                bb#set_phis ((Phi (lhs, rhs)) :: bb#get_phis);
                lst
        | _ as s ->
                s :: lst
        in
        bb#set_seq (List.fold_left on_stmt [] (List.rev bb#get_seq))
    in
    List.iter move_in_bb cfg#block_list;
    cfg

