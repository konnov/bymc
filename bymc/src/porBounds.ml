(*
 * Computing completeness bounds using partial orders.
 *
 * The idea is introduced in:
 *
 * 	 Igor Konnov, Helmut Veith, Josef Widder.
 *   On the Completeness of Bounded Model Checking for Threshold-Based
 *   Distributed Algorithms: Reachability. CONCUR'14.
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

(* Our graphs are relatively small (up to 10k nodes).
   Thus, we are using the fast implementation with matrices.
 *)
module MGraph = Graph.Imperative.Matrix.Digraph
module MGraphOper = Graph.Oper.I(MGraph)
module MGTop = Graph.Topological.Make(MGraph)
module MGSCC = Graph.Components.Make(MGraph)
module MClassic = Graph.Classic.I(MGraph)


(** Complement a graph represented with a matrix.
    The standard operation from ocamlgraph fails.
 *)
let complement g =
    let n = MGraph.nb_vertex g in
    let comp = MGraph.make n in
    let add i j =
        if not (MGraph.mem_edge g i j)
        then MGraph.add_edge comp i j
    in
    List.iter (fun i -> List.iter (add i) (range 0 n)) (range 0 n);
    comp


module PSetMap = Map.Make (struct
 type t = PSet.t
 let compare = PSet.compare
end)


module PSetEltMap = Map.Make (struct
 type t = PSet.elt
 let compare = PSet.compare_elt
end)


(* To store pairs of sets, e.g., pre+post of one rule and post of the other.
   Wahnsinn! *)
module P2Set = Set.Make (struct
 type t = PSet.t * PSet.t
 let compare (a, b) (c, d) =
     let r = PSet.compare a c in
     if r = 0
     then PSet.compare b d
     else r
end)


module ExprSet = Set.Make (struct
 type t = token expr
 let compare a b = String.compare (SpinIrImp.expr_s a) (SpinIrImp.expr_s b)
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

(* we have two lock types: unlocking (e.g., x >= t) and locking (e.g., x < f) *)
type lock_t = Lock | Unlock

(* TODO: this is not a milestone as per definition,
    but a candidate for a milestone. Rename it.
 *)
type mstone_t = string * PSet.elt * token expr * lock_t


let print_milestone lockt (name, id, m, _) =
    log INFO (sprintf "  %s (%s): %s" name
        (PSet.str (PSet.add id (PSet.empty))) (SpinIrImp.expr_s m))


(* a deps for numerous dependencies we collect here *)
module D = struct
    type deps_t = {
        (* control flow graph with rules as the vertices and the flow relation
           expressing the control flow
         *)
        fg: MGraph.t;
        
        (* map a unique condition id to its expression in Spin *)
        cond_map: (Spin.token SpinIr.expr) PSetEltMap.t;
 
        (* map a unique action id to its expression in Spin *)
        act_map: (Spin.token SpinIr.expr) PSetEltMap.t;

        (* map a rule number to a set of conditions required to enable it *)
        rule_pre: PSet.t IntMap.t;

        (* map a rule number to a set of actions the capture its postcondition *)
        rule_post: PSet.t IntMap.t;

        (* the mask of milestone candidates *)
        mile_mask: PSet.t;
        (* basic conditions to be unlocked *)
        uconds: mstone_t list;
        (* basic conditions to be locked *)
        lconds: mstone_t list;

        (* implication relation between the conditions of the same type *)
        cond_imp: PSet.t PSetEltMap.t;
    }

    let empty = {
        cond_map = PSetEltMap.empty; act_map = PSetEltMap.empty;
        rule_pre = IntMap.empty; rule_post = IntMap.empty;
        uconds = []; lconds = []; cond_imp = PSetEltMap.empty;
        mile_mask = PSet.empty;
        fg = MGraph.make 1
    }

    let conds c = c.uconds @ c.lconds
end

type path_elem_t =
    | MaybeMile
        of (mstone_t (* cond. *) * int (* rule_no *) list (* assoc. rules *))
    | Seg of int (* rule_no *) list


type path_t = path_elem_t list    

type rule_nos_t = int list

(* instead of constructing plain paths, we construct a tree *)
module T = struct
    (** a semi-linear path schema represented as a tree *)
    type schema_tree_t =
        | Leaf of rule_nos_t (** segment *)
        | Node of rule_nos_t (** segment *) * schema_branch_t list (** branches *)

    (** and a branch of a tree *)
    and schema_branch_t = {
        cond_after: mstone_t;   (** the condition guarding the branch *)
        cond_rules: rule_nos_t; (** the possible rules that are fired with this condition *)
        subtree: schema_tree_t  (** the following subtree *)
    }
end
   

let print_tree out tree =
    let rec print level = function
        | T.Leaf seg ->
            fprintf out "%s" (String.make level ' ');
            fprintf out "[ ";
            List.iter (fun r -> fprintf out " %d " r) seg;
            fprintf out " ]\n"

        | T.Node (seg, branches) ->
            fprintf out "%s" (String.make level ' ');
            fprintf out "[ ";
            List.iter (fun r -> fprintf out " %d " r) seg;
            fprintf out " ]\n";

            List.iter (each_branch (level + 2)) branches

    and each_branch level { T.cond_after; T.cond_rules; T.subtree } =
        let (name, _, _, _) = cond_after in
        let rules_s = str_join " | " (List.map int_s cond_rules) in
        fprintf out "%s" (String.make level ' ');
        fprintf out "%s: (%s)\n" name rules_s;
        print (level + 2) subtree
    in 
    print 0 tree;
    fprintf out "\n"


let tree_leafs_count tree = 
    let rec f = function
        | T.Leaf _ -> 1
        | T.Node (_, bs) ->
            List.fold_left (+)
                0 (List.map (fun b -> f b.T.subtree) bs)
    in
    f tree


let compute_flow sk =
    let flowg = MGraph.make sk.Sk.nrules in
    let outgoing = Hashtbl.create sk.Sk.nrules in
    let addi (i, r) =
        MGraph.add_vertex flowg i;
        if Hashtbl.mem outgoing r.Sk.src
        then Hashtbl.replace outgoing r.Sk.src (i :: (Hashtbl.find outgoing r.Sk.src))
        else Hashtbl.add outgoing r.Sk.src [i]
    in
    List.iter addi (lst_enum sk.Sk.rules);
    let add_flow (i, r) =
        let each_succ j = MGraph.add_edge flowg i j in
        try List.iter each_succ (Hashtbl.find outgoing r.Sk.dst)
        with Not_found -> ()
    in
    List.iter add_flow (lst_enum sk.Sk.rules);
    (*IGraph.dot_output flowg (sprintf "flow-%s.dot" sk.Sk.name);*)
    flowg


(* create a single segment that consists of topologically sorted
   rules. Only the cycles of size 1 and 2 are dealt with for now.
 *)
(* TODO: deal with long cycles! *)    
let make_segment sk flowg =
    let add n rules = (MGraph.V.label n) :: rules in
    List.rev (MGTop.fold add flowg [])


let rec decompose_guard cs = function
    | BinEx (AND, l, r) ->
        decompose_guard (decompose_guard cs l) r
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


let compute_unlocking not_flowplus lockt solver sk
        condmap rule_pre actmap rule_post =
    (* The set of type P2Set keeps the pre- and postconditions that
       has been already explored. As many rules are assigned the same
       pair of pre- and postconditions, this significantly reduces the
       runtime. *)

    (* enumerate all the edges in not_flowplus and fill rule_to_conds *)
    let collect_milestones src dst (edges_seen, checked, milestones) =
        let src, dst = if lockt = Lock then dst, src else src, dst in
        let left_no = MGraph.V.label src in
        let left = List.nth sk.Sk.rules left_no in
        let right_no = MGraph.V.label dst in
        let right = List.nth sk.Sk.rules right_no in
        let right_pre_set = IntMap.find right_no rule_pre in
        let left_pre_set = IntMap.find left_no rule_pre in
        let left_post_set = IntMap.find left_no rule_post in

        let left_pre_post = PSet.union left_pre_set left_post_set in 
        let lr_pair = (right_pre_set, left_pre_post) in
        let is_seen = P2Set.mem lr_pair edges_seen in

        if not is_seen && left_no <> right_no && not (is_c_true right.Sk.guard)
        then
            let conds =
                List.filter (fun (id, _) -> PSet.mem id right_pre_set)
                    (PSetEltMap.bindings condmap) in

            let each_cond (checked, mset) (c_id, c) =
                (* action + condition *)
                let cond_and_left = (PSet.singleton c_id, left_pre_post) in
                let plus_checked = P2Set.add cond_and_left checked in
                if not (P2Set.mem cond_and_left checked)
                then if does_r_affect_cond solver sk.Sk.shared lockt left c
                    then (plus_checked, PSet.add c_id mset)
                    else (plus_checked, mset)
                else (checked, mset)
            in
            let new_checked, new_mset =
                List.fold_left each_cond (checked, milestones) conds
            in
            (P2Set.add lr_pair edges_seen, new_checked, new_mset)
        else (edges_seen, checked, milestones)
    in

    let _, _, mstone_set =
        MGraph.fold_edges collect_milestones not_flowplus
            (P2Set.empty, P2Set.empty, PSet.empty)
    in
    let mstones =
        List.filter (fun (id, _) -> PSet.mem id mstone_set)
        (PSetEltMap.bindings condmap)
    in
    let map i (m_id, cond) =
        if lockt = Lock
        then (sprintf "L%d" i, m_id, cond, lockt)
        else (sprintf "U%d" i, m_id, cond, lockt)
    in
    List.map2 map (range 0 (List.length mstones)) mstones


(* assign a set of condition ids to a rule *)
let compute_pre sk =
    let map_cond exp (cmap, rcmap, condset) =
        let exp_s = SpinIrImp.expr_s exp in
        if StrMap.mem exp_s rcmap
        then cmap, rcmap, (PSet.add (StrMap.find exp_s rcmap) condset)
        else let new_id = PSet.new_thing () in
        begin
            (PSetEltMap.add new_id exp cmap,
             StrMap.add exp_s new_id rcmap,
             PSet.add new_id condset)
        end
    in
    let add_set (rmap, cmap, rcmap) i r =
        let guard_conds = decompose_guard ExprSet.empty r.Sk.guard in
        let new_cmap, new_rcmap, condset =
            ExprSet.fold map_cond guard_conds (cmap, rcmap, PSet.empty) in
        let new_rmap = IntMap.add i condset rmap in
        (new_rmap, new_cmap, new_rcmap)
    in
    let rule_pre, cond_map, _ =
        List.fold_left2 add_set
            (IntMap.empty, PSetEltMap.empty, StrMap.empty)
            (range 0 sk.Sk.nrules) sk.Sk.rules
    in
    cond_map, rule_pre


(* assign a set of action ids to a rule *)
let compute_post sk =
    let map_cond (amap, ramap, condset) exp =
        let exp_s = SpinIrImp.expr_s exp in
        if StrMap.mem exp_s ramap
        then amap, ramap, (PSet.add (StrMap.find exp_s ramap) condset)
        else let new_id = PSet.new_thing () in
            (PSetEltMap.add new_id exp amap,
             StrMap.add exp_s new_id ramap,
             PSet.add new_id condset)
    in
    let add_set (rmap, amap, ramap) i r =
        let new_amap, new_ramap, condset =
            List.fold_left map_cond (amap, ramap, PSet.empty) r.Sk.act in
        let new_rmap = IntMap.add i condset rmap in
        (new_rmap, new_amap, new_ramap)
    in
    let rule_post, act_map, _ =
        List.fold_left2 add_set
            (IntMap.empty, PSetEltMap.empty, StrMap.empty)
            (range 0 sk.Sk.nrules) sk.Sk.rules
    in
    act_map, rule_post


let compute_cond_implications solver shared uconds lconds =
    let does_cond_imply (lname, _, left, llockt) (rname, _, right, rlockt) =
        if llockt <> rlockt
        then false (* do not compare conditions of different type *)
        else begin
            solver#push_ctx;
            if llockt = Unlock
            then ignore (solver#append_expr
                (UnEx (NEG, (BinEx (IMPLIES, left, right)))))
            else ignore (solver#append_expr
                (UnEx (NEG, (BinEx (IMPLIES, right, left)))));
            let res = solver#check in
            solver#pop_ctx;
            not res
        end
    in
    let each_cond map (name, id, exp, lockt) =
        let locks = if lockt = Lock then lconds else uconds in
        let implications =
            List.filter (does_cond_imply (name, id, exp, lockt)) locks in
        let add s (_, id, _, _) = PSet.add id s in
        let set = List.fold_left add PSet.empty implications in
        PSetEltMap.add id set map
    in
    (* run the solver *)
    solver#push_ctx;
    let nat_type = new data_type SpinTypes.TUNSIGNED in
    List.iter (fun v -> solver#append_var_def v nat_type) shared;
    let impl_map =
        List.fold_left each_cond PSetEltMap.empty (uconds @ lconds) in
    solver#pop_ctx;
    impl_map


(* find and deps various dependencies *)    
let compute_deps solver sk =
    let fg = compute_flow sk in
    let nflow = MGraph.nb_edges fg in
    logtm INFO (sprintf "> %d transition flow dependencies" nflow);
    logtm INFO "> Computing the transitive closure...";
    let fgp = MGraphOper.transitive_closure ~reflexive:true fg in
    (*
        (* dump only the small graphs *)
    logtm INFO "Writing the flow graphs...";
    MGraph.dot_output fg (sprintf "flow-%s.dot" sk.Sk.name);
    MGraph.dot_output fgp (sprintf "flowplus-%s.dot" sk.Sk.name);
    *)
    let not_flowplus = complement fgp in
    logtm INFO (sprintf "> constructing preconditions...");
    let cond_map, rule_pre = compute_pre sk in
    logtm INFO (sprintf "> found %d preconditions..." (PSetEltMap.cardinal cond_map));
    logtm INFO (sprintf "> constructing postconditions...");
    let act_map, rule_post = compute_post sk in
    logtm INFO (sprintf "> found %d postconditions..." (PSetEltMap.cardinal act_map));

    logtm INFO (sprintf "> constructing unlocking milestones...");
    let umiles = compute_unlocking not_flowplus Unlock solver sk
        cond_map rule_pre act_map rule_post in
    let n_umiles = List.length umiles in
    logtm INFO (sprintf "> %d unlocking milestones" n_umiles);
    List.iter (print_milestone Unlock) umiles;

    logtm INFO (sprintf "> constructing locking milestones...");
    let lmiles = compute_unlocking not_flowplus Lock solver sk
        cond_map rule_pre act_map rule_post in
    let n_lmiles = List.length lmiles in
    logtm INFO (sprintf "> %d locking milestones" n_lmiles);
    List.iter (print_milestone Lock) lmiles;

    logtm INFO (sprintf "> constructing implications...");
    let cond_imp = compute_cond_implications solver sk.Sk.shared umiles lmiles
    in
    logtm INFO (sprintf "> constructing strongly-connected components...");
    let print_scc scc =
        log INFO (sprintf "    > SCC of size %d" (List.length scc))
    in
    let sccs =
        List.filter (fun l -> (List.length l) > 1) (MGSCC.scc_list fg) in
    log INFO (sprintf "    > found %d non-trivial SCCs..." (List.length sccs));
    List.iter print_scc sccs;
    let add m (_, id, _, _) = PSet.add id m in
    let mile_mask = List.fold_left add PSet.empty lmiles in
    let mile_mask = List.fold_left add mile_mask umiles in
    {   D.cond_map; D.act_map; D.lconds = lmiles; D.uconds = umiles;
        D.fg; D.rule_pre; D.rule_post; D.cond_imp; D.mile_mask }


(* for each condition find all the other conditions that are not immediately
   unlocked/locked by it. This gives us a tree of choices.
 *)
let find_successors deps =
    let succ = Hashtbl.create 10 in
    let is_succ l r =
        let lname, lid, _, _ = l and rname, rid, _, _ = r in
        let l_imp_r = PSet.mem rid (PSetEltMap.find lid deps.D.cond_imp) in
        if l_imp_r && lname <> rname
        then log INFO
            (sprintf "Lock/Unlock subsumption: %s always implies %s" lname rname);
        not l_imp_r (* the right condition may succeed the left one *)
    in
    let lconds = deps.D.lconds and uconds = deps.D.uconds in
    let each_cond lockt (lname, id, c, t) =
        let followers =
            if lockt = Unlock
            then lconds @ (List.filter (is_succ (lname, id, c, t)) uconds)
            else uconds @ (List.filter (is_succ (lname, id, c, t)) lconds)
        in
        Hashtbl.replace succ c followers
    in
    List.iter (each_cond Unlock) uconds;
    List.iter (each_cond Lock) lconds;
    succ


(* compute the length of the longest accelerated path *)
let find_max_bound nrules guards_card deps succ =
    let umiles = deps.D.uconds and lmiles = deps.D.lconds in
    let exclude m m_id guard_set card =
        if PSet.mem m_id guard_set
        then begin
            Debug.trace Trc.bnd
                (fun _ ->
                    sprintf " threw away %d of %s\n" card (SpinIrImp.expr_s m));
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
        let nmiles = List.length path in
        let nsegs = 1 + nmiles in
        let segs =
            throw_locked 1 [guards_card] (List.map (fun _ -> guards_card) (range 1 nsegs)) path in
        let seg_cost seg = PSetMap.fold count_cards seg 0 in
        let cost =
            nmiles + List.fold_left (fun sum seg -> sum + (seg_cost seg)) 0 segs
        in
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


let get_cond_impls deps cond_id lockt =
    let collect_locked rhs set (_, lhs, _, _) =
        let imps = PSetEltMap.find lhs deps.D.cond_imp in
        if PSet.mem rhs imps (* lhs -> rhs *)
        then PSet.add lhs set
        else set
    in
    if lockt = Unlock
    then PSetEltMap.find cond_id deps.D.cond_imp
    else List.fold_left (collect_locked cond_id) PSet.empty deps.D.lconds


let is_rule_locked deps uset lset rule_no =
    let pre = PSet.inter deps.D.mile_mask (IntMap.find rule_no deps.D.rule_pre)
    in
    PSet.subseteq pre uset                     (* everything is unlocked *)
        && PSet.is_empty (PSet.inter pre lset) (* and nothing is locked *)
    

(* filter out the locked/unlocked rules *)    
let rec filter_path deps conds lockt path =
    let rec f uset lset = function
    | [] -> []

    | (MaybeMile ((_, id, _, lt), _) as m) :: tl ->
        if lt <> lockt
        then m :: (f uset lset tl)
        else (* from now on id is locked (unlocked),
                and whatever implies it, is locked (unlocked) too *)
            let uset, lset =
                if lt = Unlock
                then (PSet.union uset (get_cond_impls deps id lt)), lset
                else uset, (PSet.union lset (get_cond_impls deps id lt))
            in
            m :: (f uset lset tl)

    | (Seg rule_nos) :: tl ->
        (Seg (List.filter (is_rule_locked deps uset lset) rule_nos))
            :: (f uset lset tl)
    in
    f PSet.empty PSet.empty path


(** add all possible rules that are labeled with a specific condition *)    
let unfold_conds sk deps path =
    (* TODO: more careful analysis is required to remove redundant rules *)
    let is_guarded_with (_, cond_no, _, _) rule_no =
        let conds =
            PSet.inter deps.D.mile_mask (IntMap.find rule_no deps.D.rule_pre) in
        PSet.mem cond_no conds
    in
    let rec f = function
    | [] -> []
    | (Seg _) as s :: tl -> s :: (f tl)
    | (MaybeMile (cond, _)) :: tl ->
         let all_guarded_with = 
             List.filter (is_guarded_with cond) (range 0 sk.Sk.nrules) in
         (MaybeMile (cond, all_guarded_with)) :: (f tl)
    in
    f path


(**
   Compute the tree of representative executions.

   Here we compute a semilinear regular path scheme (SLPS),
   see, e.g., Flat counter automata almost everywhere.
   The difference is that we do not represent ALL executions with SLPS,
   but only the representative ones.
 *)
let compute_slps_tree sk deps =
    let full_segment = make_segment sk deps.D.fg in
    let uconds = deps.D.uconds and lconds = deps.D.lconds in

    let rec build_tree uset lset =
        let is_guarded_with cond_id rule_no =
            let conds =
                PSet.inter deps.D.mile_mask (IntMap.find rule_no deps.D.rule_pre)
            in
            PSet.mem cond_id conds
        in
        let each_cond accum (name, cond_id, expr, lockt) =
            if (PSet.mem cond_id uset) || (PSet.mem cond_id lset)
            then accum (* already covered *)
            else (* create a branch *)
                let all_guarded_with = 
                    List.filter (is_guarded_with cond_id) (range 0 sk.Sk.nrules)
                in
                let new_uset, new_lset =
                    if lockt = Unlock
                    then (PSet.union uset (get_cond_impls deps cond_id lockt)), lset
                    else uset, (PSet.union lset (get_cond_impls deps cond_id lockt))
                in
                let subtree = build_tree new_uset new_lset in
                let branch = 
                    {
                        T.cond_after = (name, cond_id, expr, lockt);
                        T.cond_rules = all_guarded_with;
                        subtree
                    }
                in
                branch :: accum
        in
        let seg = List.filter (is_rule_locked deps uset lset) full_segment in
        let branches = List.fold_left each_cond [] (uconds @ lconds) in
        if branches = []
        then T.Leaf seg
        else T.Node (seg, branches)
    in
    build_tree PSet.empty PSet.empty


let collect_actions accum sk =
    let rec each_rule set r = ExprSet.add (list_to_binex AND r.Sk.act) set in
    List.fold_left each_rule accum sk.Sk.rules


(* count how many times every guard (not a subformula of it!) appears in a rule *)
let count_guarded sk deps =
    let each_rule map i r =
        let pre = PSet.inter deps.D.mile_mask (IntMap.find i deps.D.rule_pre) in
        if PSetMap.mem pre map
        then PSetMap.add pre (1 + (PSetMap.find pre map)) map
        else PSetMap.add pre 1 map
    in
    List.fold_left2 each_rule PSetMap.empty (range 0 sk.Sk.nrules) sk.Sk.rules


let compute_diam solver dom_size sk =
    logtm INFO (sprintf "> found %d locations..." sk.Sk.nlocs);
    logtm INFO (sprintf "> found %d rules..." sk.Sk.nrules);

    let deps = compute_deps solver sk in

    logtm INFO (sprintf "> Computing bounds for %s..." sk.Sk.name);

    let guards_card = count_guarded sk deps in
    let print_potential_mstone g n =
        log INFO (sprintf "  potential milestone (%s) -> %d times" (PSet.str g) n)
    in
    log INFO (sprintf "> The occurences of potential milestones:");
    PSetMap.iter print_potential_mstone guards_card;

    let miles_succ = find_successors deps in (* TODO: get rid of it *)

    let n_lmiles = List.length deps.D.lconds 
    and n_umiles = List.length deps.D.uconds in
    let bound = (1 + n_lmiles + n_umiles) * sk.Sk.nrules + (n_lmiles + n_umiles) in
    log INFO (sprintf "> the bound for %s is %d = (1 + %d + %d) * %d + %d"
        sk.Sk.name bound n_umiles n_lmiles sk.Sk.nrules (n_lmiles + n_umiles));
    log INFO (sprintf "> the counter abstraction bound for %s is %d = %d * %d"
        sk.Sk.name (bound * (dom_size - 1)) bound (dom_size - 1));

    let max_bound = find_max_bound sk.Sk.nrules guards_card deps miles_succ in
    log INFO (sprintf "> the mild bound for %s is %d" sk.Sk.name max_bound);
    log INFO (sprintf "> the mild counter abstraction bound for %s is %d"
        sk.Sk.name (max_bound * (dom_size - 1)))


let make_schema_tree solver sk =
    logtm INFO "Building the schema tree...";
    logtm INFO (sprintf "> found %d locations..." sk.Sk.nlocs);
    logtm INFO (sprintf "> found %d rules..." sk.Sk.nrules);

    let deps = compute_deps solver sk in

    let guards_card = count_guarded sk deps in
    let print_potential_mstone g n =
        log INFO (sprintf "  potential milestone (%s) -> %d times" (PSet.str g) n)
    in
    log INFO (sprintf "> The occurences of potential milestones:");
    PSetMap.iter print_potential_mstone guards_card;

    log INFO ("> Computing the schema tree...");
    let tree = compute_slps_tree sk deps in

    log INFO ("> SLPS is written to slps-paths.txt");
    let out = open_out "slps-paths.txt" in
    print_tree out tree;
    close_out out;

    tree

