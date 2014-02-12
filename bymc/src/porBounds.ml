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


let does_r_unlock solver shared r t =
    let mk_layer i =
        let h = Hashtbl.create (List.length shared) in
        let add v =
            let nv = v#copy (sprintf "%s$%d" v#get_name i) in
            Hashtbl.replace h v#id nv
        in
        List.iter add shared;
        h
    in
    let var_to_layer l v = Var (Hashtbl.find l v#id) in
    let l0, l1 = mk_layer 0, mk_layer 1 in
    let e_to_l l e = map_vars (var_to_layer l) e in
    let mk_assign = function
        | BinEx (ASGN, lhs, rhs) ->
            BinEx (ASGN, e_to_l l1 lhs, e_to_l l0 rhs)
        | _ as e -> e
    in
    let r_eff = list_to_binex AND (List.map mk_assign r.Sk.act) in
    false


let compute_unlocking solver sk =
    let g = IGraph.create () in
    let add_flow (i, r) =
        let each (j, t) =
            if i <> j && does_r_unlock solver sk.Sk.shared r t
            then () (* profit *)
        in
        List.iter each (lst_enum sk.Sk.rules)
    in
    List.iter add_flow (lst_enum sk.Sk.rules);
    IGraph.dot_output g (sprintf "unlocking-%s.dot" sk.Sk.name);
    g


let compute_diam solver sk =
    let fg = compute_flow sk in
    let ug = compute_unlocking solver sk in
    ()


