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

(* as ocamlgraph does distinguish two vertices objects that are labelled the
   same, we have to create a universum of all these vertices (and edges).
 *)

module U = struct
    let vertices = Hashtbl.create 1000
    let edges = Hashtbl.create 10000

    let mkv i =
        try Hashtbl.find vertices i
        with Not_found ->
            let v = IGraph.V.create i in
            Hashtbl.replace vertices i v; v

    let mke i lab j =
        try Hashtbl.find edges (i, lab, j)
        with Not_found ->
            let e = IGraph.E.create (mkv i) lab (mkv j) in
            Hashtbl.replace edges (i, lab, j) e; e
end


type lock_t = Lock | Unlock

let compute_flow sk =
    let flowg = IGraph.create () in
    let outgoing = Hashtbl.create sk.Sk.nrules in
    let addi (i, r) =
        IGraph.add_vertex flowg (U.mkv i);
        if Hashtbl.mem outgoing r.Sk.src
        then Hashtbl.replace outgoing r.Sk.src (i :: (Hashtbl.find outgoing r.Sk.src))
        else Hashtbl.add outgoing r.Sk.src [i]
    in
    List.iter addi (lst_enum sk.Sk.rules);
    let add_flow (i, r) =
        let each_succ j = IGraph.add_edge_e flowg (U.mke i 0 j) in
        try List.iter each_succ (Hashtbl.find outgoing r.Sk.dst)
        with Not_found -> ()
    in
    List.iter add_flow (lst_enum sk.Sk.rules);
    IGraph.dot_output flowg (sprintf "flow-%s.dot" sk.Sk.name);
    flowg


let does_r_affect_t solver query_cache shared lockt i r j t =
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

    let is_cached, cached_result =
        try (true, Hashtbl.mem query_cache (lockt, t_pre0, r_post0))
        with Not_found -> (false, false)
    in
    if is_cached
    then cached_result
    else begin
        solver#push_ctx;
        let nat_type = new data_type SpinTypes.TUNSIGNED in
        let decl h v =
            let lv = Hashtbl.find h v#id in
            solver#append_var_def lv nat_type
        in
        (* the variable declarations must be moved out of the function *)
        List.iter (decl l0) shared; List.iter (decl l1) shared;
        ignore (solver#comment (sprintf "does rule %d %s rule %d?"
                i (if lockt = Unlock then "unlock" else "lock") j));
        if not (is_c_true r_pre0)
        then begin
            ignore (solver#comment "r is enabled");
            ignore (solver#append_expr r_pre0); (* r is enabled *)
        end;
        if lockt = Unlock
        then begin
            ignore (solver#comment "t is disabled");
            ignore (solver#append_expr (UnEx (NEG, t_pre0))); (* t is not *)
            ignore (solver#comment "r fires");
            ignore (solver#append_expr r_post0); (* r fires *)
            ignore (solver#comment "t is now enabled");
            ignore (solver#append_expr t_pre1); (* t becomes enabled *)
        end else if lockt = Lock
        then begin
            ignore (solver#comment "t is enabled");
            ignore (solver#append_expr (t_pre0)); (* t is enabled *)
            ignore (solver#comment "r fires");
            ignore (solver#append_expr r_post0); (* r fires *)
            ignore (solver#comment "t is now disabled");
            ignore (solver#append_expr (UnEx (NEG, t_pre1))); (* t becomes disabled *)
        end else begin
            raise (Failure "Unsupported lock type")
        end;
        let res = solver#check in
        solver#pop_ctx;

        Hashtbl.replace query_cache (lockt, t_pre0, r_post0) res;
        res
    end


let compute_unlocking lockt is_to_keep solver sk =
    let graph = IGraph.create () in
    let add_rule i =
        IGraph.add_vertex graph (U.mkv i)
    in
    List.iter add_rule (range 0 sk.Sk.nrules);
    let query_cache = Hashtbl.create 1024 in
    let add_flow (i, r) =
        let each (j, t) =
            if i <> j && not (is_c_true t.Sk.guard)
                && does_r_affect_t solver query_cache sk.Sk.shared lockt i r j t
                && is_to_keep i j
            then IGraph.add_edge_e graph (U.mke i 0 j)
        in
        List.iter each (lst_enum sk.Sk.rules)
    in
    List.iter add_flow (lst_enum sk.Sk.rules);
    let fname = if lockt = Unlock then "unlocking" else "locking" in
    IGraph.dot_output graph (sprintf "%s-%s.dot" fname sk.Sk.name);
    graph


let compute_diam solver dom_size sk =
    logtm INFO (sprintf "> there are %d locations..." sk.Sk.nlocs);
    logtm INFO (sprintf "> there are %d rules..." sk.Sk.nrules);
    logtm INFO (sprintf "> computing bounds for %s..." sk.Sk.name);
    let fg = compute_flow sk in
    let nflow = IGraph.nb_edges fg in
    logtm INFO (sprintf "> %d transition flow dependencies" nflow);
    let fgp = IGraphOper.transitive_closure ~reflexive:false fg in
    IGraph.dot_output fg (sprintf "flow-%s.dot" sk.Sk.name);
    IGraph.dot_output fgp (sprintf "flowplus-%s.dot" sk.Sk.name);
    let is_in_flowplus i j =
        (* find_vertex is inefficient, but the authors of ocamlgraph don't
           leave us any other choice... *)
        IGraph.mem_edge fgp (IGraph.find_vertex fgp i) (IGraph.find_vertex fgp j)
    in
    let is_backward i j = not (is_in_flowplus i j) && (is_in_flowplus j i)
    in
    logtm INFO (sprintf "> constructing unlocking transition dependencies...");
    let ug = compute_unlocking Unlock is_backward solver sk in
    logtm INFO (sprintf "> %d unlocking transition dependencies" (IGraph.nb_edges ug));
    let nbackward = IGraph.nb_edges ug in
    logtm INFO (sprintf "> %d backward unlocking transition dependencies" nbackward);
    IGraph.dot_output ug (sprintf "unlocking-flowplus-%s.dot" sk.Sk.name);

    let is_forward i j = not (is_in_flowplus j i) && (is_in_flowplus i j)
    in
    logtm INFO (sprintf "> constructing locking transition dependencies...");
    let lg = compute_unlocking Lock is_forward solver sk in
    logtm INFO (sprintf "> %d locking transition dependencies" (IGraph.nb_edges lg));
    let nforward = IGraph.nb_edges lg in
    logtm INFO (sprintf "> %d forward locking transition dependencies" nforward);
    IGraph.dot_output lg (sprintf "locking-flowplus-%s.dot" sk.Sk.name);

    (* XXX: the bound is lower than that, find the identical conditions
      instead of just backward edges *)
    let bound = (1 + nbackward + nforward) * sk.Sk.nrules in
    log INFO (sprintf "> the bound for %s is %d = (1 + %d + %d) * %d"
        sk.Sk.name bound nbackward nforward sk.Sk.nrules);
    log INFO (sprintf "> the counter abstraction bound for %s is %d = %d * %d"
        sk.Sk.name (bound * (dom_size - 1)) bound (dom_size - 1));
    bound


