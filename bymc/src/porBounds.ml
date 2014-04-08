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

type lock_t = Lock | Unlock

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


let does_r_affect_t solver shared lockt r t =
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
    let rec assign_layers = function
        | UnEx (NEXT, Var v) -> var_to_layer l1 v
        | UnEx (NEXT, _) as e ->
                raise (Failure ("malformed next: " ^ (SpinIrImp.expr_s e)))
        | Var v -> var_to_layer l0 v
        | UnEx (t, e) -> UnEx (t, assign_layers e)
        | BinEx (t, l, r) -> BinEx (t, assign_layers l, assign_layers r)
        | e -> e
    in
    let r_post0 = list_to_binex AND (List.map assign_layers r.Sk.act) in
    let r_pre0 = e_to_l l0 r.Sk.guard in
    let t_pre0 = e_to_l l0 t.Sk.guard in
    let t_pre1 = e_to_l l1 t.Sk.guard in
    solver#push_ctx;
    let nat_type = new data_type SpinTypes.TUNSIGNED in
    let decl h v =
        let lv = Hashtbl.find h v#id in
        solver#append_var_def lv nat_type
    in
    (* the variable declarations must be moved out of the function *)
    List.iter (decl l0) shared; List.iter (decl l1) shared;
    if not (is_c_true r_pre0)
    then ignore (solver#append_expr r_pre0); (* r is enabled *)
    if lockt = Unlock
    then begin
        ignore (solver#append_expr (UnEx (NEG, t_pre0))); (* t is not *)
        ignore (solver#append_expr r_post0); (* r fires *)
        ignore (solver#append_expr t_pre1); (* t becomes enabled *)
    end else if lockt = Lock
    then begin
        ignore (solver#append_expr (t_pre0)); (* t is enabled *)
        ignore (solver#append_expr r_post0); (* r fires *)
        ignore (solver#append_expr (UnEx (NEG, t_pre1))); (* t becomes disabled *)
    end else begin
        raise (Failure "Unsupported lock type")
    end;
    let res = solver#check in
    solver#pop_ctx;
    res


let compute_unlocking lockt solver sk =
    let graph = IGraph.create () in
    let add_rule i =
        IGraph.add_vertex graph (IGraph.V.create i)
    in
    List.iter add_rule (range 0 sk.Sk.nrules);
    let add_flow (i, r) =
        let each (j, t) =
            if i <> j && not (is_c_true t.Sk.guard)
                && does_r_affect_t solver sk.Sk.shared lockt r t
            then IGraph.add_edge graph
                (IGraph.find_vertex graph i) (IGraph.find_vertex graph j)
        in
        List.iter each (lst_enum sk.Sk.rules)
    in
    List.iter add_flow (lst_enum sk.Sk.rules);
    let fname = if lockt = Unlock then "unlocking" else "locking" in
    IGraph.dot_output graph (sprintf "%s-%s.dot" fname sk.Sk.name);
    graph


let compute_diam solver sk =
    logtm INFO (sprintf "> there are %d rules..." sk.Sk.nrules);
    logtm INFO (sprintf "> computing bounds for %s..." sk.Sk.name);
    let fg = compute_flow sk in
    let nflow = IGraph.nb_edges fg in
    logtm INFO (sprintf "> %d flow edges" nflow);
    let not_fgc =
        IGraphOper.complement (IGraphOper.transitive_closure ~reflexive:false fg) in
    logtm INFO (sprintf "> constructing unlocking edges...");
    let ug = compute_unlocking Unlock solver sk in
    logtm INFO (sprintf "> %d unlocking edges" (IGraph.nb_edges ug));
    let diff = IGraphOper.intersect ug not_fgc in
    let nbackward = IGraph.nb_edges diff in
    logtm INFO (sprintf "> %d backward unlocking edges" nbackward);
    IGraph.dot_output diff
        (sprintf "unlocking-flowplus-%s.dot" sk.Sk.name);

    logtm INFO (sprintf "> constructing locking edges...");
    let lg = compute_unlocking Lock solver sk in
    logtm INFO (sprintf "> %d locking edges" (IGraph.nb_edges lg));
    let diff = IGraphOper.intersect (IGraphOper.mirror lg) not_fgc in
    let nforward = IGraph.nb_edges diff in
    logtm INFO (sprintf "> %d forward locking edges" nforward);
    IGraph.dot_output diff
        (sprintf "locking-flowplus-%s.dot" sk.Sk.name);

    (* XXX: the bound is lower than that, find the identical conditions
      instead of just backward edges
     *)
    let bound = (1 + nbackward + nforward) * sk.Sk.nrules in
    log INFO (sprintf "> the bound for %s is %d = (1 + %d + %d) * %d"
        sk.Sk.name bound nbackward nforward sk.Sk.nrules);
    bound


