(*
 * Computing execution bounds using partial order reduction.
 *
 * Igor Konnov, 2014
 *)

open Printf

open Accums
open Debug
open Spin
open SpinIr
open SymbSkel

module IGraph = Graph.Pack.Digraph
module IGraphOper = Graph.Oper.I(IGraph)

let compute_flow sk =
    let flowg = IGraph.create () in
    let incoming = Hashtbl.create sk.Sk.nrules in
    let addi (i, r) =
        IGraph.add_vertex flowg (IGraph.V.create i);
        if Hashtbl.mem incoming r.Sk.src
        then Hashtbl.replace incoming r.Sk.src (i :: (Hashtbl.find incoming r.Sk.src))
        else Hashtbl.add incoming r.Sk.src [i]
    in
    List.iter addi (lst_enum sk.Sk.rules);
    let add_flow (i, r) =
        let each_succ j =
            IGraph.add_edge flowg
                (IGraph.find_vertex flowg i) (IGraph.find_vertex flowg j)
        in
        try List.iter each_succ (Hashtbl.find incoming r.Sk.dst)
        with Not_found -> ()
    in
    List.iter add_flow (lst_enum sk.Sk.rules);
    IGraph.dot_output flowg (sprintf "flow-%s.dot" sk.Sk.name);
    flowg


let does_r_unlock_t solver shared r t =
    let mk_layer i =
        let h = Hashtbl.create (List.length shared) in
        let add v =
            let nv = v#copy (sprintf "%s$%d" v#get_name i) in
            Hashtbl.replace h v#id nv
        in
        List.iter add shared;
        h
    in
    let var_to_layer l v =
        try
            if not v#is_symbolic
            then Var (Hashtbl.find l v#id)
            else Var v (* keep the parameters *)
        with Not_found ->
            raise (Failure ("No layer variable for " ^ v#get_name ))
    in
    let l0, l1 = mk_layer 0, mk_layer 1 in
    let e_to_l l e = map_vars (var_to_layer l) e in
    let mk_assign = function
        | BinEx (ASGN, lhs, rhs) ->
            BinEx (EQ, e_to_l l1 lhs, e_to_l l0 rhs)
        | _ as e -> e
    in
    let r_post0 = list_to_binex AND (List.map mk_assign r.Sk.act) in
    let r_pre0 = e_to_l l0 r.Sk.guard in
    let t_pre0 = e_to_l l0 t.Sk.guard in
    let t_pre1 = e_to_l l1 t.Sk.guard in
    solver#push_ctx;
    let nat_type = new data_type SpinTypes.TUNSIGNED in
    let decl h v =
        let lv = Hashtbl.find h v#id in
        solver#append_var_def lv nat_type
    in
    (* the variable declarations may be moved out of the function *)
    List.iter (decl l0) shared; List.iter (decl l1) shared;
    if not (is_c_true r_pre0)
    then ignore (solver#append_expr r_pre0); (* r is enabled *)
    ignore (solver#append_expr (UnEx (NEG, t_pre0))); (* t is not *)
    ignore (solver#append_expr r_post0); (* r fires *)
    ignore (solver#append_expr t_pre1); (* t becomes enabled *)
    let res = solver#check in
    solver#pop_ctx;
    res


let compute_unlocking solver sk =
    let g = IGraph.create () in
    let add_rule i =
        IGraph.add_vertex g (IGraph.V.create i)
    in
    List.iter add_rule (range 0 sk.Sk.nrules);
    let add_flow (i, r) =
        let each (j, t) =
            if i <> j && not (is_c_true t.Sk.guard)
                && does_r_unlock_t solver sk.Sk.shared r t
            then IGraph.add_edge g
                (IGraph.find_vertex g i) (IGraph.find_vertex g j)
        in
        List.iter each (lst_enum sk.Sk.rules)
    in
    List.iter add_flow (lst_enum sk.Sk.rules);
    IGraph.dot_output g (sprintf "unlocking-%s.dot" sk.Sk.name);
    g

let compute_diam solver sk =
    log INFO (sprintf "> computing bounds for %s..." sk.Sk.name);
    let fg = compute_flow sk in
    let nflow = IGraph.nb_edges fg in
    log INFO (sprintf "> %d flow edges" nflow);
    let fgc = IGraphOper.transitive_closure ~reflexive:false fg in
    log INFO (sprintf "> constructing unlocking edges...");
    let ug = compute_unlocking solver sk in
    log INFO (sprintf "> %d unlocking edges" (IGraph.nb_edges ug));
    let diff = IGraphOper.intersect ug (IGraphOper.complement fgc) in
    let nbackward = IGraph.nb_edges diff in
    log INFO (sprintf "> %d backward unlocking edges" nbackward);
    IGraph.dot_output diff
        (sprintf "unlocking-flowplus-%s.dot" sk.Sk.name);
    (* XXX: the bound is lower than that, find the identical conditions
      instead of just backward edges
     *)
    let bound = (1 + nbackward) * sk.Sk.nrules in
    log INFO (sprintf "> the bound for %s is %d" sk.Sk.name bound);
    bound


