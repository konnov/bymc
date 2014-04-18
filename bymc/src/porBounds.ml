(*
 * Computing execution bounds using partial order reduction.
 *
 * Igor Konnov, 2014
 *)

open Big_int
open Printf

open Accums
open Debug
open Spin
open SpinIr
open SymbSkel

module IGraph = Graph.Pack.Digraph
module IGraphOper = Graph.Oper.I(IGraph)

(* set membership as division by prime numbers *)
module PSet = struct
    type elt = big_int
    type t = big_int

    let before = ref (big_int_of_int 2) (* a number before the next prime *)

    (* this is supposed to work with very small prime numbers *)
    let new_thing () =
        let rec is_prime num n2 d =
            if ge_big_int d n2
            then true
            else if eq_big_int (mod_big_int num d) zero_big_int
                then false
                else is_prime num n2 (succ_big_int d)
        in
        let rec search num =
            let n2 = succ_big_int (div_big_int num (big_int_of_int 2)) in
            if is_prime num n2 (big_int_of_int 2)
            then num
            else search (succ_big_int num)
        in
        let new_prime = search (!before) in
        before := succ_big_int new_prime;
        new_prime

    let str = string_of_big_int        

    let empty = unit_big_int (* it corresponds to an empty set *)

    let mem e set =
        eq_big_int (mod_big_int set e) zero_big_int

    let add e set =
        if mem e set
        then set 
        else mult_big_int set e

    let remove e set =
        if mem e set
        then div_big_int set e
        else set

    let compare = compare_big_int

  end

module PSetMap = Map.Make (struct
 type t = PSet.t
 let compare = PSet.compare
end)


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

let rec collect_guard_elems cs = function
    | BinEx (AND, l, r) ->
        collect_guard_elems (collect_guard_elems cs l) r
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


let does_r_affect_cond solver shared lockt r cond =
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
    res


let compute_unlocking not_flowplus lockt solver sk =
    (* every condition is assigned a number *)
    let conds_to_num = Hashtbl.create 1024 in
    let cond_no c =
        try Hashtbl.find conds_to_num c
        with Not_found ->
            let no = Hashtbl.length conds_to_num in
            Hashtbl.add conds_to_num c no;
            no
    in
    (* every rule has a set of associated conditions *)
    let rule_to_conds = Hashtbl.create 1024 in
    let collect_rule_conds (i, r) =
        let conds = collect_guard_elems ExprSet.empty r.Sk.guard in
        let with_no c = (cond_no c, c) in
        Hashtbl.replace rule_to_conds i
            (List.map with_no (ExprSet.elements conds))
    in
    let get_rule_conds i =
        try Hashtbl.find rule_to_conds i
        with Not_found -> raise (Failure ("No rule " ^ (int_s i)))
    in
    List.iter collect_rule_conds (lst_enum sk.Sk.rules);

    (* this table keeps relation (rule, {UNLOCKS, DOESNOT}, conds) *)
    let rule_to_conds = Hashtbl.create 1024 in
    let is_cached ri ci = Hashtbl.mem rule_to_conds (ri, ci) in
    let cache ri ci res = Hashtbl.replace rule_to_conds (ri, ci) res in

    (* enumerate all the edges in not_flowplus and fill rule_to_conds *)
    let collect_milestones src dst milestones =
        let src, dst = if lockt = Lock then dst, src else src, dst in
        let left_no = IGraph.V.label src in
        let left = List.nth sk.Sk.rules left_no in
        let right_no = IGraph.V.label dst in
        let right = List.nth sk.Sk.rules right_no in
        if left_no <> right_no && not (is_c_true right.Sk.guard)
        then begin
            let conds = get_rule_conds right_no in
            let each_cond mset (c_no, c) =
                if not (is_cached left_no c_no)
                then begin
                    let res =
                        does_r_affect_cond solver sk.Sk.shared lockt left c in
                    cache left_no c_no res;
                    if res
                    then ExprSet.add c mset
                    else mset
                end
                else mset
            in
            List.fold_left each_cond milestones conds
        end
        else milestones
    in

    let mstones =
        IGraph.fold_edges collect_milestones not_flowplus ExprSet.empty
    in
    let map i m =
        if lockt = Lock
        then (sprintf "L%d" i, PSet.new_thing (), m, lockt)
        else (sprintf "U%d" i, PSet.new_thing (), m, lockt)
    in
    List.map2 map (range 0 (ExprSet.cardinal mstones)) (ExprSet.elements mstones)


let print_milestone lockt (name, id, m, _) =
    log INFO (sprintf "  %s (%s): %s" name (PSet.str id) (SpinIrImp.expr_s m))


(* count how many times every guard (not a subformula of it!) appears in a rule *)
(* actually we use characteristic numbers that are products of primes *)
let count_guarded milestones map r =
    let mk_set conds =
        List.fold_left (fun set (_, id, _, _) -> PSet.add id set)
            PSet.empty
            (List.filter (fun (_, _, m, _) -> ExprSet.mem m conds) milestones)
    in
    let cond_set = mk_set (collect_guard_elems ExprSet.empty r.Sk.guard) in
    if PSetMap.mem cond_set map
    then PSetMap.add cond_set (1 + (PSetMap.find cond_set map)) map
    else PSetMap.add cond_set 1 map


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
    let each_cond lockt (lname, id, c, t) =
        let followers =
            if lockt = Unlock
            then lmiles @ (List.filter (is_succ Unlock (lname, id, c, t)) umiles)
            else umiles @ (List.filter (is_succ Lock (lname, id, c, t)) lmiles)
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


let find_max_bound nrules guards_card umiles lmiles succ =
    let exclude m m_id guard_set card =
        if PSet.mem m_id guard_set
        then begin
            Debug.trace Trc.bnd
                (fun _ -> sprintf " threw away %d of %s\n"
                    card (SpinIrImp.expr_s m));
            0
        end
        else card
    in
    let count_cards _ card total = total + card in

    let estimate_path max_cost path =
        let rec throw_locked level lsegs rsegs mstones =
            match mstones with
            | [] -> lsegs @ rsegs (* one segment was to the right of m *)
            | (n, id, m, t) :: tl ->
                 Debug.trace Trc.bnd
                    (fun _ -> Printf.sprintf " %s %s\n" (String.make level '>') n);
                 if t = Unlock
                 then let nlsegs =
                     List.map (fun seg -> PSetMap.mapi (exclude m id) seg) lsegs in
                    throw_locked (level + 1) ((List.hd rsegs) :: nlsegs) (List.tl rsegs) tl
                 else let nrsegs =
                     List.map (fun seg -> PSetMap.mapi (exclude m id) seg) rsegs in
                    throw_locked (level + 1) ((List.hd nrsegs) :: lsegs) (List.tl nrsegs) tl
        in
        let nsegs = 1 + (List.length path) in
        let segs =
            throw_locked 1 [guards_card] (List.map (fun _ -> guards_card) (range 1 nsegs)) path in
        let seg_cost seg = PSetMap.fold count_cards seg 0 in
        let cost = List.fold_left (fun sum seg -> sum + (seg_cost seg)) 0 segs in
        Debug.trace Trc.bnd
            (fun _ -> sprintf " -----> nsegs = %d, cost = %d" nsegs cost);
        max cost max_cost
    in

    (* construct alternations of conditions and call a function on a leaf *)
    let rec build_paths f max_cost rev_prefix =
        let n, id, m, _ = List.hd rev_prefix in
        let each_succ cost (nn, id, s, t) =
            if not (List.exists (fun (name, _, _, _) -> nn = name) rev_prefix)
            then build_paths f cost ((nn, id, s, t) :: rev_prefix)
            else (f cost (List.rev rev_prefix))
        in
        let succs = Hashtbl.find succ m in
        if succs = []
        then f max_cost (List.rev rev_prefix)
        else List.fold_left each_succ max_cost succs
    in
    let each_branch max_cost (n, id, m, t) =
        logtm INFO (sprintf " -----> root %s (max_cost = %d)" n max_cost);
        let new_cost = build_paths estimate_path max_cost [(n, id, m, t)] in
        logtm INFO (sprintf " -----> %s: cost = %d" n new_cost);
        max max_cost new_cost
    in
    List.fold_left each_branch nrules (umiles @ lmiles)


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
    logtm INFO (sprintf "> constructing unlocking milestones...");
    let umiles = compute_unlocking not_flowplus Unlock solver sk in
    let n_umiles = List.length umiles in
    logtm INFO (sprintf "> %d unlocking milestones" n_umiles);
    List.iter (print_milestone Unlock) umiles;

    logtm INFO (sprintf "> constructing locking milestones...");
    let lmiles = compute_unlocking not_flowplus Lock solver sk in
    let n_lmiles = List.length lmiles in
    logtm INFO (sprintf "> %d locking milestones" n_lmiles);
    List.iter (print_milestone Lock) lmiles;

    let guards_card =
        List.fold_left (count_guarded (umiles @ lmiles)) PSetMap.empty sk.Sk.rules
    in
    let print_guard g n =
        log INFO (sprintf "  guard (%s) -> %d times" (PSet.str g) n)
    in
    PSetMap.iter print_guard guards_card;


    let bound = (1 + n_lmiles + n_umiles) * sk.Sk.nrules in
    log INFO (sprintf "> the bound for %s is %d = (1 + %d + %d) * %d"
        sk.Sk.name bound n_umiles n_lmiles sk.Sk.nrules);
    log INFO (sprintf "> the counter abstraction bound for %s is %d = %d * %d"
        sk.Sk.name (bound * (dom_size - 1)) bound (dom_size - 1));

    let miles_succ = compute_cond_impl solver sk.Sk.shared umiles lmiles in
    let max_bound = find_max_bound sk.Sk.nrules guards_card umiles lmiles miles_succ in
    log INFO (sprintf "> the mild bound for %s is %d" sk.Sk.name max_bound);
    log INFO (sprintf "> the mild counter abstraction bound for %s is %d"
        sk.Sk.name (max_bound * (dom_size - 1)));

    bound


