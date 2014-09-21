(* Single static assignment form.
 *
 * This module is written in Dubrovnik next to Adriatic sea.
 * So it may have more bugs than the other modules!
 *
 * Igor Konnov, 2012-2013.
 *
 * TODO: hide all the implementation details under the interface.
 *)

open Printf

open Accums
open Analysis
open Cfg
open Debug
open Spin
open SpinIr
open SpinIrImp

module IGraph = Graph.Pack.Digraph
module IGraphColoring = Graph.Coloring.Make(IGraph)
module IGraphOper = Graph.Oper.I(IGraph)

module VarStruct = struct
    type t = var
    let compare lhs rhs =
        if lhs#id = rhs#id
        then lhs#mark - rhs#mark
        else lhs#id - rhs#id

    let hash v = v#id * v#mark

    let equal lhs rhs = (lhs#id = rhs#id && lhs#mark = rhs#mark)
end

module VarDigraph = Graph.Imperative.Digraph.Concrete(VarStruct)
module VarGraph = Graph.Imperative.Graph.Concrete(VarStruct)

module VarOper = Graph.Oper.I(VarDigraph)
module VarColoring = Graph.Coloring.Make(VarGraph)

module IntStruct = struct
    type t = int
    let default = 0
    let compare a b = a - b
    let hash i = i
    let equal a b = (a = b)
end

module IIGraph =
    Graph.Imperative.Digraph.ConcreteBidirectionalLabeled
        (IntStruct)(IntStruct)

module MatrixG = Graph.Imperative.Matrix.Digraph

exception Var_not_found of string

let mark_in = 0
let mark_out = max_int

(* Graph as an adjacency matrix. It seems to be much
   more efficient when computing transitive closures.
   NOTE: This is my first functor. Functors are cool!
 *)
module GraphAsMatrix =
    functor (G: Graph.Sig.G) ->
        struct
            module V2I = Map.Make(G.V)
            module I2V = IntMap
            module MG = Graph.Imperative.Matrix.Digraph

            type t = {
                v2i: int V2I.t; i2v: G.V.t I2V.t; mg: MG.t
            }

            let make (g: G.t) =
                let mg = MG.make (G.nb_vertex g) in
                let add v (s, i) = (I2V.add i v s, i + 1) in
                let i2v, _ = G.fold_vertex add g (I2V.empty, 0) in
                let add v (s, i) = (V2I.add v i s, i + 1) in
                let v2i, _ = G.fold_vertex add g (V2I.empty, 0) in
                let add_edge f t =
                    let fi = V2I.find f v2i in
                    let ti = V2I.find t v2i in
                    MG.add_edge mg fi ti
                in
                G.iter_edges add_edge g;
                { v2i = v2i; i2v = i2v; mg = mg }

            let to_v m i = I2V.find i m.i2v
            let to_i m v = V2I.find v m.v2i
            let mx_g m = m.mg
        end


module BlockGasM = GraphAsMatrix(BlockG)
module MGO = Graph.Oper.I(BlockGasM.MG)


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


(* Find phis of the form x3 = phi(x2, x2) that can be eliminated.
   Note that some of these phis must be kept intact, as the
   sequential dependency will require that. Additionaly, IN and OUT
   versions are always preserved.

   Surprisingly, this function is very long. Any idea how to make
   it shorter???
 *)
let find_redundant_phis cfg var =
    (* edge labels show the type of the dependency *)
    let phi_dep = 0 and seq_dep = 1 in

    (* keep markings and dependencies among them *)
    let vertices = Hashtbl.create 8 in
    let depg = IIGraph.create () in
    let node i =
        try Hashtbl.find vertices i
        with Not_found ->
            let v = IIGraph.V.create i in
            Hashtbl.replace vertices i v;
            IIGraph.add_vertex depg v;
            v
    in
    let each_block b =
        let each_stmt last_mark = function
            | Expr (_, Phi (lhs, rhs)) ->
                trace Trc.ssa
                    (fun _ -> sprintf "b%d: %s#%d = phi(%s)"
                        b#label lhs#mangled_name lhs#mark
                        (str_join "," (List.map
                            (fun v -> string_of_int v#mark) rhs)));
                let fst = List.hd rhs in
                if lhs#id = var#id
                then if List.for_all (fun o -> o#mark = fst#mark) rhs
                then begin
                    (* x_T3 = phi(x_T2, x_T2), declare phi dep. *)
                    let e = IIGraph.E.create
                            (node fst#mark) phi_dep (node lhs#mark) in
                    IIGraph.add_edge_e depg e;
                    lhs#mark
                end else begin
                    (* x_T3 = phi(x_T1, x_T2), declare sequential dep.*)
                    let add_every r =
                        let e = IIGraph.E.create
                                (node r#mark) seq_dep (node lhs#mark) in
                        IIGraph.add_edge_e depg e
                    in
                    List.iter add_every rhs;
                    lhs#mark
                end else
                    last_mark

            | Expr (_, BinEx (ASGN, Var lhs, rhs)) ->
                if lhs#id = var#id
                then begin
                    if last_mark <> -1
                    then let e =
                        IIGraph.E.create
                            (node last_mark) seq_dep (node lhs#mark) in
                        IIGraph.add_edge_e depg e;
                        lhs#mark
                    else
                        lhs#mark
                end else
                    last_mark

            | _ -> last_mark
        in
        ignore (List.fold_left each_stmt (-1) b#get_seq)
    in
    List.iter each_block cfg#block_list;
    (* the dependencies are known, try the reduction *)
    let subs = Hashtbl.create 8 in
    (* update the renaming function transitively,
       using 'was' for 'what' and 'mit' for 'with',
       as 'with' is a keyword *)
    let add_sub mit was =
        let mit =
            if Hashtbl.mem subs mit
            then Hashtbl.find subs mit
            else mit
        in
        let update a b =
            if b = was && a <> mit
            then begin
                trace Trc.ssa (fun _ ->
                    sprintf "add_sub* %d -> %d -> %d" a b mit);
                Hashtbl.replace subs a mit
            end
        in
        if was <> mit
        then begin
            trace Trc.ssa
                (fun _ -> sprintf "add_sub %d -> %d" was mit);
            Hashtbl.replace subs was mit;
            Hashtbl.iter update subs
        end
    in
    (* find the renaming for each vertex *)
    let inspect_vertex v =
        trace Trc.ssa (fun _ -> sprintf "inspect %d" v);
        let pred = IIGraph.pred depg v in
        let is_phi_dep e = (phi_dep = (IIGraph.E.label e)) in
        if List.for_all is_phi_dep (IIGraph.pred_e depg v)
                && (List.length pred) <> 0
        then begin
            let neighb = v :: pred in
            let emin = List.fold_left min max_int neighb in
            let repr = emin in
            (* substitute the neighborhood with repr *)
            List.iter (add_sub repr) neighb
        end else
            trace Trc.ssa (fun _ -> sprintf "%d is rigid" v)
    in
    IIGraph.iter_vertex inspect_vertex depg;
    (* IN and OUT must be left in the graph *)
    let revert a =
        trace Trc.ssa (fun _ -> sprintf "revert %d" a);
        try 
            let b = Hashtbl.find subs a in
            Hashtbl.remove subs a; (* there is no substitutes by a *)
            add_sub a b (* do transitive reversal *)
        with Not_found -> ()
    in
    revert mark_in; (* change the direction *)
    revert mark_out;
    (* unbind in -> out and out -> in *)
    Hashtbl.remove subs mark_in;
    Hashtbl.remove subs mark_out;
    subs


(*
 It appears that the Cytron's algorithm can produce redundant phi functions like
 x_2 = phi(x_1, x_1, x_1). Here we remove them.

 XXX: proof-read it, there must be definitely some bugs inside!
 *)
let optimize_ssa cfg vars =
    let each_var v =
        trace Trc.ssa (fun _ ->
            sprintf "optimize_ssa.each_var %s" v#mangled_name);
        (* substitutions *)
        let subs = find_redundant_phis cfg v in
        let sub what =
            if what#id <> v#id
            then what
            else
                try let new_mark = Hashtbl.find subs what#mark in
                    what#set_mark new_mark;
                    what
                with Not_found -> what
        in
        let subex what = Var (sub what) in
        let map_s s = map_expr_in_lir_stmt (map_vars subex) s in
        let each_block b = b#set_seq (List.map map_s b#get_seq) in
        List.iter each_block cfg#block_list;
        let each_phi l = function
            | Expr (id, Phi (lhs, rhs)) as s ->
                if lhs#id <> v#id
                then s :: l
                else
                    let fst = List.hd rhs in
                    let all_eq =
                        List.for_all (fun o -> o#mark = fst#mark) rhs
                    in
                    let fst = sub fst and lhs = sub lhs in
                    if all_eq
                    then if fst#mark = lhs#mark
                        (* redundant phi function *)
                        then l
                        (* copy the variable, but no phi function *)
                        else (Expr (id, BinEx (ASGN, Var lhs, Var fst)))
                             :: l
                    else s :: l (* we need the phi function *)

            | _ as s -> s :: l
        in
        let each_block b =
            b#set_seq (List.fold_left each_phi [] (List.rev b#get_seq))
        in
        List.iter each_block cfg#block_list
    in
    List.iter each_var vars;
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
    else if v#mark = mark_in
    then Var (copy v (sprintf "%s_IN" v#get_name))
    else if v#mark = mark_out
    then Var (copy v (sprintf "%s_OUT" v#get_name))
    else Var (copy v (sprintf "%s_T%d" v#get_name v#mark))


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

(* Graph.Coloring.coloring stucks unpredictably on small graphs
  (e.g., 30 nodes, 6 colors). Use SMT solver to do the coloring.
  Our graphs are not large, so this approach works well enough.
  For larger examples we can try a SAT solver.
*)
let find_coloring solver graph ncolors =
    solver#push_ctx;
    solver#set_need_evidence true;
    let color_tp = new data_type SpinTypes.TINT in
    color_tp#set_range 0 ncolors;
    let vars = Hashtbl.create ncolors in
    let add_vertex v =
        let c = new_var (sprintf "_nclr%d" v#mark) in
        Hashtbl.replace vars v#mark c;
        solver#append_var_def c color_tp
    in
    let add_edge v w =
        if v#mark <> w#mark
        then let vc = Hashtbl.find vars v#mark
             and wc = Hashtbl.find vars w#mark in
            (* the colors of the vertices connected with the edges
               must be different. That's it. *)
            ignore (solver#append_expr (BinEx (NE, Var vc, Var wc)))
    in
    VarGraph.iter_vertex add_vertex graph;
    VarGraph.iter_edges add_edge graph;
    let tab = Hashtbl.create ncolors in
    let each_expr = function
        | BinEx (EQ, Var v, Const i) ->
            let len = String.length v#get_name in
            let pref = if len > 5 then String.sub v#get_name 0 5 else "" in
            if pref = "_nclr"
            then begin
                let index =
                    int_of_string (String.sub v#get_name 5 (len - 5)(* _nclr *))
                in
                Hashtbl.replace tab index (1 + i)
                    (* a color from 1 to k, as in Graph.Coloring *)
            end
        
        | _ -> ()
    in
    let lookup name =
        let len = String.length name in
        let pref = if len > 5 then String.sub name 0 5 else "" in
        if pref = "_nclr"
        then begin
            let index = int_of_string (String.sub name 5 (len - 5) (* _nclr *))
            in
            try Hashtbl.find vars index 
            with Not_found ->
                raise (Var_not_found (sprintf "var not found %d" index))
        end else (* a redundant variable, make something up *)
            new_var name
    in
    let found =
        if solver#check
        then begin (* parse evidence, XXX: inefficient *)
            List.iter each_expr (solver#get_model lookup);
            assert((Hashtbl.length tab) > 0);
            true
        end else
            false
    in
    solver#set_need_evidence false;
    solver#pop_ctx;
    (found, tab)


let print_dot filename var_graph =
    let ig = IGraph.create () in
    let addv v = IGraph.add_vertex ig (IGraph.V.create v#mark) in
    VarDigraph.iter_vertex addv var_graph;
    let adde v w =
        IGraph.add_edge ig
            (IGraph.find_vertex ig v#mark) (IGraph.find_vertex ig w#mark)
    in
    (* FIXME: inefficient due to find_vertex *)
    VarDigraph.iter_edges adde var_graph;
    IGraph.dot_output ig filename


(* for every basic block, find the starting indices of the variables,
   i.e., such indices that have not been used in immediate dominators.
 *)
let reduce_indices solver mx var =
    let get_bb_copies bb = get_var_copies var bb#seq in
    let depg = VarDigraph.create () in
    let add_vertex var = VarDigraph.add_vertex depg var in
    let add_copies i =
        let block = BlockGasM.to_v mx i in
        let copies = get_bb_copies block in
        List.iter add_vertex copies
    in
    trace Trc.ssa
        (fun _ -> sprintf "add %d vertices to depg of %s"
            (BlockGasM.MG.nb_vertex (BlockGasM.mx_g mx)) var#mangled_name);
    BlockGasM.MG.iter_vertex add_copies (BlockGasM.mx_g mx);
    
    (* add dependencies *)
    let add_dep v1 v2 =
        if v1#mark <> v2#mark
        then VarDigraph.add_edge depg v1 v2
    in
    let add_bb_deps src =
        let copies = get_bb_copies (BlockGasM.to_v mx src) in
        (* all copies are dependent in the block *)
        List.iter (fun v -> List.iter (add_dep v) copies) copies;
        let add_succ succ =
            let scopies = get_bb_copies (BlockGasM.to_v mx succ) in
            List.iter (fun v -> List.iter (add_dep v) scopies) copies
        in
        List.iter add_succ (BlockGasM.MG.succ (BlockGasM.mx_g mx) src)
    in
    trace Trc.ssa
        (fun _ -> sprintf "add edges to depg of %s" var#mangled_name);
    BlockGasM.MG.iter_vertex add_bb_deps mx.BlockGasM.mg;

    (* all assignment along one path depend on each other *)
    trace Trc.ssa (fun _ ->
        sprintf "add_transitive_closure on %s, nodes=%d, edges=%d"
        var#mangled_name (VarDigraph.nb_vertex depg) (VarDigraph.nb_edges depg));
    ignore (VarOper.add_transitive_closure ~reflexive:false depg);
    (* remove self-loops that can be introduced by transitive closure *)
    trace Trc.ssa (fun _ -> "print_dot");
    VarDigraph.iter_vertex (fun v -> VarDigraph.remove_edge depg v v) depg;
    print_dot (sprintf "deps-%s.dot" var#get_name) depg;

    (* NOTE: coloring works only on undirected graphs,
       so we have to convert it to an undirected graph. *)
    let g = VarGraph.create () in
    VarDigraph.iter_edges (fun v w -> VarGraph.add_edge g v w) depg;

    (* try to find minimal coloring via binary search *)
    let ecoloring = Hashtbl.create 1 (*VarColoring.H.create 1*) in
    let rec find_min_colors left right = (* binary search *)
        let k = (left + right) / 2 in
        trace Trc.ssa (fun _ ->
            sprintf "%s: n=%d, left=%d, right=%d, k=%d\n"
            var#get_name (VarGraph.nb_vertex g) left right k);
        if left > right
        then (0, ecoloring)
        else let found, h = find_coloring solver g k
            (* ALTERNATIVE: ocamlgraph coloring, extremely slow
            try true, VarColoring.coloring g k
            with _ -> false, ecoloring *)
        in
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
    let max_colors = VarGraph.nb_vertex g in
    trace Trc.ssa (fun _ -> "coloring");
    let ncolors, coloring =
        if max_colors <> 0
        then find_min_colors 1 max_colors
        else max_colors, ecoloring
    in
    assert (max_colors = 0 || ncolors <> 0);
    trace Trc.ssa (fun _ -> "remarking");
    (* find new marks. NOTE: we do not replace colors in place, as this
       might corrupt the vertex iterator. *)
    let fold v l =
        if v#mark <> mark_in && v#mark <> mark_out
        then (v, Hashtbl.find coloring v#mark
            (*VarColoring.H.find coloring v*)) :: l
        else (v, v#mark) :: l
    in
    let new_marks = VarGraph.fold_vertex fold g [] in
    List.iter (fun (v, c) -> v#set_mark c) new_marks;
    trace Trc.ssa (fun _ -> "print_dot");
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
        then v  (* TODO: what about atomic propositions? *)
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
                    (* introduce a fresh version *)
                    let nv = intro_var v in
                    (* BUGFIX: Keep havoc, as it is going to be used
                       in reduce_indices. See ssaTest#test_mk_ssa_havoc *)
                    Havoc (id, nv)
            | _ as s -> s
        in
        let on_stmt lst s =
            let new_rhs = replace_rhs s in
            (replace_lhs new_rhs) :: lst
        in
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
        then begin
            (* declare the variables on the top of the stack
               to be output variables *)
            let each_set_mark_out v = (s_top v)#set_mark mark_out in
            List.iter each_set_mark_out extern_vars
        end;
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
        List.iter pop_stmt bb_old_seq;
    in
    search 0


(* (in-place) transformation of CFG to SSA.  *)
let mk_ssa solver tolerate_undeclared_vars extern_vars intern_vars
        new_sym_tab new_type_tab cfg =
    trace Trc.ssa (fun _ -> "mk_ssa_cytron");
    mk_ssa_cytron tolerate_undeclared_vars extern_vars intern_vars cfg;
    let rename_block bb =
        let map_s s =
            map_expr_in_lir_stmt
                (map_vars (add_mark_to_name new_sym_tab new_type_tab)) s in
        let ns = List.map map_s bb#get_seq in
        bb#set_seq ns
    in
    (* We need to track dependencies along paths;
       compute the graph closure. Additional hassle due to slow
       computations on basic blocks (in ocamlgraph)
     *)
    let bcfg = cfg#as_block_graph in
    trace Trc.ssa (fun _ -> sprintf "bcfg to adjacency matrix");
    let mx = BlockGasM.make bcfg in
    trace Trc.ssa (fun _ ->
        sprintf "add_transitive_closure of mx.mg, nodes=%d, edges=%d"
        (BlockG.nb_vertex bcfg) (BlockG.nb_edges bcfg));
    ignore (MGO.add_transitive_closure ~reflexive:false mx.BlockGasM.mg);

    (* reduce the number of variable indices using coloring *)
    trace Trc.ssa (fun _ -> "reduce_indices");
    List.iter (reduce_indices solver mx) intern_vars;
    List.iter (reduce_indices solver mx) extern_vars;
    trace Trc.ssa (fun _ -> "optimize_ssa");
    (* remove redundant phi funcs *)
    ignore (optimize_ssa cfg (intern_vars @ extern_vars));

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

