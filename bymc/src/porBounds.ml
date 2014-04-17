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


module ExprSet = Set.Make (struct
 type t = token expr
 let compare a b = String.compare (SpinIrImp.expr_s a) (SpinIrImp.expr_s b)
end)

let rec collect_guard_conds cs = function
    | BinEx (AND, l, r) ->
        collect_guard_conds (collect_guard_conds cs l) r
    | e ->
        ExprSet.add e cs

let collect_conditions accum sk =
    let rec collect cs = function
    | BinEx (AND, l, r) ->
        collect (collect cs l) r
    | e ->
        ExprSet.add e cs
    in
    let rec each_rule set r = collect set r.Sk.guard in
    List.fold_left each_rule accum sk.Sk.rules


let does_r_affect_cond solver query_cache shared lockt r cond =
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
    let cond0 = e_to_l l0 cond in
    let cond1 = e_to_l l1 cond in

    let is_cached, cached_result =
        try (true, Hashtbl.find query_cache (lockt, cond0, r_pre0, r_post0))
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
        if not (is_c_true r_pre0)
        then begin
            ignore (solver#comment "r is enabled");
            ignore (solver#append_expr r_pre0); (* r is enabled *)
        end;
        if lockt = Unlock
        then begin
            ignore (solver#comment "cond is disabled");
            ignore (solver#append_expr (UnEx (NEG, cond0))); (* cond is not *)
            ignore (solver#comment "r fires");
            ignore (solver#append_expr r_post0); (* r fires *)
            ignore (solver#comment "t is now enabled");
            ignore (solver#append_expr cond1); (* cond becomes enabled *)
        end else if lockt = Lock
        then begin
            ignore (solver#comment "t is enabled");
            ignore (solver#append_expr (cond0)); (* cond is enabled *)
            ignore (solver#comment "r fires");
            ignore (solver#append_expr r_post0); (* r fires *)
            ignore (solver#comment "t is now disabled");
            ignore (solver#append_expr (UnEx (NEG, cond1))); (* cond becomes disabled *)
        end else begin
            raise (Failure "Unsupported lock type")
        end;
        let res = solver#check in
        solver#pop_ctx;

        Hashtbl.replace query_cache (lockt, cond0, r_pre0, r_post0) res;
        res
    end


let compute_unlocking not_flowplus lockt solver sk =
    let graph = IGraph.create () in
    let add_rule i =
        IGraph.add_vertex graph (U.mkv i)
    in
    List.iter add_rule (range 0 sk.Sk.nrules);
    let query_cache = Hashtbl.create 1024 in
    let collect_milestones src dst milestones =
        let src, dst = if lockt = Lock then dst, src else src, dst in
        let left = List.nth sk.Sk.rules (IGraph.V.label src) in
        let right = List.nth sk.Sk.rules (IGraph.V.label dst) in
        if src <> dst && not (is_c_true right.Sk.guard)
        then begin
            let conds = collect_guard_conds ExprSet.empty right.Sk.guard in
            let affected = ExprSet.filter
                (does_r_affect_cond solver query_cache sk.Sk.shared lockt left)
                conds
            in
            ExprSet.union affected milestones
        end
        else milestones
    in
    let mstones =
        IGraph.fold_edges collect_milestones not_flowplus ExprSet.empty
    in
    let rec count_guarded rules m =
        match rules with
        | [] -> 0
        | hd :: tl ->
            if hd.Sk.guard = m
            then 1 + (count_guarded tl m)
            else count_guarded tl m
    in
    let map i m =
        let cnt = count_guarded sk.Sk.rules m in
        if lockt = Lock
        (* cnt rules will be locked after the milestone *)
        then (sprintf "L%d" i, 0, m, cnt)
        (* cnt rules are locked before the milestone *)
        else (sprintf "U%d" i, cnt, m, 0)
    in
    List.map2 map (range 0 (ExprSet.cardinal mstones)) (ExprSet.elements mstones)


let compute_cond_impl solver shared umiles lmiles =
    let succ = Hashtbl.create 10 in
    let is_succ lockt (lname, _, left, _) (rname, _, right, _) =
        solver#push_ctx;
        if lockt = Unlock
        then ignore (solver#append_expr
            (UnEx (NEG, (BinEx (IMPLIES, left, right)))))
        else ignore (solver#append_expr
            (UnEx (NEG, (BinEx (IMPLIES, right, left)))));
        let res = solver#check in
        solver#pop_ctx;
        if not res && lname <> rname
        then log INFO (sprintf
            "Lock/Unlock subsumption: %s implies %s" lname rname);
        res (* left does not imply right or vice versa *)
    in
    let each_cond lockt (lname, b, c, a) =
        let followers =
            if lockt = Unlock
            then lmiles @ (List.filter (is_succ Unlock (lname, b, c, a)) umiles)
            else umiles @ (List.filter (is_succ Lock (lname, b, c, a)) lmiles)
        in
        Hashtbl.replace succ c followers
    in
    solver#push_ctx;
    let nat_type = new data_type SpinTypes.TUNSIGNED in
    List.iter (fun v -> solver#append_var_def v nat_type) shared;
    List.iter (each_cond Unlock) umiles;
    List.iter (each_cond Lock) lmiles;
    solver#pop_ctx;
    succ


let find_max_bound nrules miles succ =
    let rec enum nsegs before after prefix (n, b, m, a) =
        let nbefore = before + nrules - 1 - b * nsegs in
        let nafter = after + a in
        Printf.printf "%s%s, nbefore = %d (-%d), nafter = %d (+%d)\n"
                (String.make (nsegs * 2) ' ') n nbefore (b * nsegs) nafter a;
        let each_succ (nn, b, s, a) =
            if not (List.mem nn prefix)
            then enum (nsegs + 1) nbefore nafter (nn :: prefix) (nn, b, s, a)
            else nbefore - nafter (* leaf *)
        in
        let succs = Hashtbl.find succ m in
        if succs = []
        then nbefore - nafter
        else List.fold_left
            (fun max_cost m -> max max_cost (each_succ m))
            0 succs
    in
    let each_branch max_cost (n, b, m, a) =
        let cost = enum 1 nrules 0 [n] (n, b, m, a) in
        log INFO (sprintf " --> cost = %d" cost);
        max max_cost cost
    in
    List.fold_left each_branch nrules miles


let collect_actions accum sk =
    let rec each_rule set r = ExprSet.add (list_to_binex AND r.Sk.act) set in
    List.fold_left each_rule accum sk.Sk.rules


let compute_diam solver dom_size sk =
    logtm INFO (sprintf "> there are %d locations..." sk.Sk.nlocs);
    logtm INFO (sprintf "> there are %d rules..." sk.Sk.nrules);

    let conds = collect_conditions ExprSet.empty sk in
    logtm INFO (sprintf "> there are %d conditions..." (ExprSet.cardinal conds));

    let actions = collect_actions ExprSet.empty sk in
    logtm INFO (sprintf "> there are %d actions..." (ExprSet.cardinal actions));

    logtm INFO (sprintf "> computing bounds for %s..." sk.Sk.name);
    let fg = compute_flow sk in
    let nflow = IGraph.nb_edges fg in
    logtm INFO (sprintf "> %d transition flow dependencies" nflow);
    let fgp = IGraphOper.transitive_closure ~reflexive:true fg in
    IGraph.dot_output fg (sprintf "flow-%s.dot" sk.Sk.name);
    IGraph.dot_output fgp (sprintf "flowplus-%s.dot" sk.Sk.name);
    let not_flowplus = IGraphOper.complement fgp in
    let is_in_flowplus i j =
        (* find_vertex is inefficient, but the authors of ocamlgraph don't
           leave us any other choice... *)
        IGraph.mem_edge fgp (IGraph.find_vertex fgp i) (IGraph.find_vertex fgp j)
    in
    let is_backward i j = not (is_in_flowplus i j) (*&& (is_in_flowplus j i)*)
    in
    logtm INFO (sprintf "> constructing unlocking milestones...");
    let umiles = compute_unlocking not_flowplus Unlock solver sk in
    let n_umiles = List.length umiles in
    logtm INFO (sprintf "> %d unlocking milestones" n_umiles);
    let print_milestone lockt (name, before, m, after) =
        log INFO (sprintf "  %s (%d, %d): %s"
            name before after (SpinIrImp.expr_s m))
    in
    List.iter (print_milestone Unlock) umiles;

    let is_forward i j = not (is_in_flowplus j i) (*&& (is_in_flowplus i j)*)
    in
    logtm INFO (sprintf "> constructing locking milestones...");
    let lmiles = compute_unlocking not_flowplus Lock solver sk in
    let n_lmiles = List.length lmiles in
    logtm INFO (sprintf "> %d locking milestones" n_lmiles);
    List.iter (print_milestone Lock) lmiles;

    let bound = (1 + n_lmiles + n_umiles) * sk.Sk.nrules in
    log INFO (sprintf "> the bound for %s is %d = (1 + %d + %d) * %d"
        sk.Sk.name bound n_umiles n_lmiles sk.Sk.nrules);
    log INFO (sprintf "> the counter abstraction bound for %s is %d = %d * %d"
        sk.Sk.name (bound * (dom_size - 1)) bound (dom_size - 1));

    let miles_succ = compute_cond_impl solver sk.Sk.shared umiles lmiles in
    let max_bound = find_max_bound sk.Sk.nrules (umiles @ lmiles) miles_succ in
    log INFO (sprintf "> the mild bound for %s is %d" sk.Sk.name max_bound);
    log INFO (sprintf "> the mild counter abstraction bound for %s is %d"
        sk.Sk.name (max_bound * (dom_size - 1)));

    bound


