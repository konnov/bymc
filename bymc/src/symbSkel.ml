(*
  Extract a symbolic skeleton (a threshold automaton).

  Igor Konnov, 2014-2016
 *)

open Printf

open Accums
open Debug
open Spin
open SpinIr
open SymbExec

open Cfg
open Ssa

type qtype = QAll | QExist | QCard

(* the symbolic skeleton *)
module Sk = struct
    type rule_t = {
        src: int; dst: int; (* indices in locs *)
        guard: token expr; act: token expr list
    }

    type loc_t = int list (* variable assignments *)

    type skel_t = {
        name: string; (* just a name, e.g., the process type *)
        nlocs: int; (* the number of locations *)
        locs: loc_t list; (* the list of locations *)
        locals: var list; (* local variables *)
        shared: var list; (* shared variables *)
        params: var list; (* parameters *)
        assumes: token expr list; (* assumptions on the parameters *)
        nrules: int; (* the number of rules *)
        rules: rule_t list; (* the rules *)
        inits: token expr list; (* initialization expressions *)
        loc_vars: var IntMap.t;
            (* variables that correspond to locations,
               e.g., used in the initialization part *)
        forms: Spin.token SpinIr.expr Accums.StrMap.t; (** LTL formulas *)
    }

    let empty locals shared params =
        { name = ""; nlocs = 0; locs = [];
          locals = locals; shared = shared; params = params;
          nrules = 0; rules = []; inits = []; assumes = [];
          loc_vars = IntMap.empty; forms = StrMap.empty;
        }

    let loc_by_no sk loc_no =
        List.nth sk.locs loc_no

    let locname l =
        let s i = if i < 0 then "X" else string_of_int i in
        sprintf "loc%s" (str_join "_" (List.map s l))

    let locvar sk loc_no =
        IntMap.find loc_no sk.loc_vars

    let rec expr_s = function
        | UnEx (NEXT, Var v) -> v#get_name ^ "'"
        | UnEx (NEXT, _) as e ->
            raise (Failure ("Unexpected expression: " ^ (SpinIrImp.expr_s e)))
        | UnEx (t, e) -> sprintf "(%s%s)" (SpinIrImp.token_s t) (expr_s e)
        | BinEx (EQ as t, l, r)
        | BinEx (NE as t, l, r)
        | BinEx (LE as t, l, r)
        | BinEx (GE as t, l, r)
        | BinEx (LT as t, l, r)
        | BinEx (GT as t, l, r) -> (* no parentheses here *)
                sprintf "%s %s %s"
                    (expr_s l) (SpinIrImp.token_s t) (expr_s r) 
        | BinEx (t, l, r) ->
                sprintf "(%s %s %s)"
                    (expr_s l) (SpinIrImp.token_s t) (expr_s r) 
        | _ as e -> SpinIrImp.expr_s e

    let print out sk =
        let pexp e = fprintf out "    %s;\n" (expr_s e) in

        fprintf out "skel %s {\n" sk.name;
        let vname v = v#get_name in
        fprintf out "  local %s;\n"
            (str_join ", " (List.map vname sk.locals));
        fprintf out "  shared %s;\n"
            (str_join ", " (List.map vname sk.shared));
        fprintf out "  parameters %s;\n"
            (str_join ", " (List.map vname sk.params));
        fprintf out "  assumptions (%d) {\n" (List.length sk.assumes);
        List.iter pexp sk.assumes;
        fprintf out "  }\n\n";
        let ploc (i, l) =
            fprintf out "    %s: [%s];\n"
                (locname l) (str_join "; " (List.map int_s l))
        in
        fprintf out "  locations (%d) {\n" sk.nlocs;
        List.iter ploc (lst_enum sk.locs);
        fprintf out "  }\n\n";
        fprintf out "  inits (%d) {\n" (List.length sk.inits);
        List.iter pexp sk.inits;
        fprintf out "  }\n\n";
        let prule (i, r) =
            let loc j = locname (List.nth sk.locs j) in
            fprintf out "  %d: %s -> %s\n      when (%s)\n      do { %s };\n"
                i (loc r.src) (loc r.dst) (expr_s r.guard)
                (str_join "; " (List.map expr_s r.act))
        in
        fprintf out "  rules (%d) {\n" sk.nrules;
        List.iter prule (lst_enum sk.rules);
        fprintf out "  }\n";
        fprintf out "  specifications (%d) {\n" (StrMap.cardinal sk.forms);
        let pform name form =
            fprintf out "    %s = %s;\n" name (expr_s form);
        in
        StrMap.iter pform sk.forms;
        fprintf out "  }\n";
        fprintf out "} /* %s */\n" sk.name

    let to_file name sk =
        let f = open_out name in
        print f sk;
        close_out f
end


module VarMap = BatMap.Make (struct
    type t = var
    let compare a b = a#id - b#id
end)


(**
    Keep only those locations that are reachable from the initial locations.
    The implementation looks only at the syntactically reachable locations.
 *)
let keep_reachable sk =
    let renaming = Hashtbl.create sk.Sk.nlocs in
    let is_visited loc_no = Hashtbl.mem renaming loc_no in
    let get_new_num loc_no = Hashtbl.find renaming loc_no in
    let rec visit loc_no =
        try ignore (Hashtbl.find renaming loc_no)
        with Not_found ->
            let new_idx = Hashtbl.length renaming in
            Hashtbl.add renaming loc_no new_idx;
            let each_rule r =
                if r.Sk.src = loc_no
                then visit r.Sk.dst
            in
            List.iter each_rule sk.Sk.rules
    in
    let rev_map =
        IntMap.fold (fun i v m -> VarMap.add v i m)
        sk.Sk.loc_vars VarMap.empty
    in
    let each_init_expr = function
        | BinEx (EQ, l, r) ->
                let visit_used v =
                    try visit (VarMap.find v rev_map)
                    with Not_found -> ()
                        (* a shared variable -> ignore *)
                in
                if l <> IntConst 0 && r <> IntConst 0
                then begin
                    List.iter visit_used (SpinIr.expr_used_vars l);
                    List.iter visit_used (SpinIr.expr_used_vars r)
                end

        | _ -> ()
    in
    (* visit all locations reachable from the initial locations *)
    List.iter each_init_expr sk.Sk.inits;
    (* keep the reachable locations *)
    let loc_arr = Array.make (Hashtbl.length renaming) [] in
    let each_loc loc loc_no =
        if is_visited loc_no
        then loc_arr.(get_new_num loc_no) <- loc
    in
    let each_rule lst r =
        if not (is_visited r.Sk.src) || not (is_visited r.Sk.dst)
        then lst
        else { r with Sk.src = get_new_num r.Sk.src;
                      Sk.dst = get_new_num r.Sk.dst; } :: lst
    in
    List.iter2 each_loc sk.Sk.locs (Accums.range 0 sk.Sk.nlocs);
    let new_locs = Array.to_list loc_arr in
    let new_rules = List.fold_left each_rule [] sk.Sk.rules in
    let map_loc_var old_loc new_loc map =
        IntMap.add new_loc (IntMap.find old_loc sk.Sk.loc_vars) map
    in
    let new_loc_vars = Hashtbl.fold map_loc_var renaming IntMap.empty in
    let each_init lst e =
        let omit_unreach v =
            if not (VarMap.mem v rev_map)
            then Var v
            else if is_visited (VarMap.find v rev_map)
                then Var v
                else IntConst 0
        in
        let ne = Simplif.compute_consts (SpinIr.map_vars omit_unreach e) in
        assert (not (is_c_false ne));
        if is_c_true ne
        then lst
        else ne :: lst
    in
    let new_inits = List.fold_left each_init [] sk.Sk.inits in
    { sk with Sk.locs = new_locs; Sk.nlocs = List.length new_locs;
        Sk.rules = new_rules; Sk.nrules = List.length new_rules;
        Sk.inits = new_inits;
        Sk.loc_vars = new_loc_vars;

    }


let filter_rules f sk =
    let new_rules = List.filter f sk.Sk.rules in
    { sk with Sk.rules = new_rules; Sk.nrules = List.length new_rules }


(* auxillary functions to optimize guards *)
module I = struct
    module IGraph = Graph.Pack.Digraph

    type interval_t =
        | IntLR of Spin.token SpinIr.expr * Spin.token SpinIr.expr * Spin.token SpinIr.expr
        | IntL of Spin.token SpinIr.expr * Spin.token SpinIr.expr
        | IntR of Spin.token SpinIr.expr * Spin.token SpinIr.expr
        | SmthElse of Spin.token SpinIr.expr


    let is_smth_else = function
        | SmthElse _ -> true
        | _ -> false


    let arg_of_inter = function
        | IntLR (a, _, _) -> a
        | IntL (a, _)     -> a
        | IntR (a, _)     -> a
        | SmthElse a    -> a


    let inter_of_expr = function
        | BinEx (AND, BinEx (GE, l1, r1), BinEx (LT, l2, r2)) as e ->
            if l1 = l2
            then IntLR (l1, r1, r2)
            else SmthElse e

        | BinEx (AND, BinEx (LT, l2, r2), BinEx (GE, l1, r1)) as e ->
            if l1 = l2
            then IntLR (l1, r1, r2)
            else SmthElse e

        | BinEx (GE, l, r) ->
            IntL (l, r)

        | BinEx (LT, l, r) ->
            IntR (l, r)

        | _ as e ->
            SmthElse e


    let expr_of_inter = function
        | IntLR (a, l, r) -> BinEx (AND, BinEx (GE, a, l), BinEx (LT, a, r))

        | IntL (a, l) -> BinEx (GE, a, l)

        | IntR (a, r) -> BinEx (LT, a, r)

        | SmthElse e -> e

    let glue_intervals arg ints =
        let tab = BatHashtbl.create (List.length ints) in
        let rev = BatHashtbl.create (List.length ints) in
        let ig = IGraph.create () in
        let infminus, infplus = IGraph.V.create 0, IGraph.V.create 1 in
        let add_expr e =
            let e_s = SpinIrImp.expr_s e in
            try BatHashtbl.find rev e_s
            with Not_found ->
                let id = 2 + (BatHashtbl.length rev) in
                let vertex = IGraph.V.create id in
                BatHashtbl.add rev e_s vertex;
                BatHashtbl.add tab id e;
                vertex
        in
        let add_interval = function
            | IntL (_, l) ->
                    let v = add_expr l in
                    IGraph.add_edge_e ig (IGraph.E.create v 0 infplus)

            | IntR (_, r) ->
                    let v = add_expr r in
                    IGraph.add_edge_e ig (IGraph.E.create infminus 0 v)

            | IntLR (_, l, r) ->
                    let vl = add_expr l in
                    let vr = add_expr r in
                    assert (vl <> vr); (* no self-loops *)
                    IGraph.add_edge_e ig (IGraph.E.create vl 0 vr)

            | SmthElse _ -> raise (Failure "cannot happen")
        in
        List.iter add_interval ints;
        let each_vertex v =
            if (IGraph.V.label v) > 1 (* not infinity *)
            then begin
                let each_pred_e pe =
                    let each_succ_e se =
                        let src = IGraph.E.src pe in
                        let dst = IGraph.E.dst se in
                        (* XXX: side-effects??? *)
                        if not (IGraph.mem_edge ig src dst)
                        then IGraph.add_edge_e ig (IGraph.E.create src 0 dst);
                        IGraph.remove_edge_e ig se
                    in
                    if (IGraph.out_degree ig v) > 0
                    then begin
                        IGraph.iter_succ_e each_succ_e ig v;
                        IGraph.remove_edge_e ig pe;
                    end
                in
                IGraph.iter_pred_e each_pred_e ig v
            end
        in
        (*IGraph.dot_output ig ("before.dot");*)
        IGraph.iter_vertex each_vertex ig;
        (*IGraph.dot_output ig ("after.dot");*)

        let fold_edge src dst ints =
            if src = infminus
            then (IntR (arg, BatHashtbl.find tab (IGraph.V.label dst))) :: ints
            else if dst = infplus
            then IntL (arg, BatHashtbl.find tab (IGraph.V.label src)) :: ints
            else IntLR (arg,
                BatHashtbl.find tab (IGraph.V.label src),
                BatHashtbl.find tab (IGraph.V.label dst)) :: ints
        in
        IGraph.fold_edges fold_edge ig []


    let try_glue conjuncts =
        let smth_else, ints =
            List.partition is_smth_else (List.map inter_of_expr conjuncts) in
        let tab = BatHashtbl.create (List.length ints) in
        let add inter =
            let arg = arg_of_inter inter in
            let before = 
                try BatHashtbl.find tab arg
                with Not_found -> []
            in
            BatHashtbl.replace tab arg (inter :: before)
        in
        List.iter add ints;
        let map_each_arg result arg =
            let arg_ints = BatHashtbl.find tab arg in
            result @ (glue_intervals arg arg_ints)
        in
        let glued = BatEnum.fold map_each_arg [] (BatHashtbl.keys tab) in
        List.map expr_of_inter (glued @ smth_else)
end


(* try to optimize the guards by gluing the intervals *)
let optimize_guards sk =
    let rec collect_conjuncts acc = function
        | BinEx (OR, l, r) ->
                (collect_conjuncts (collect_conjuncts acc r) l)

        | e -> e :: acc
    in
    let rec opt = function
        | BinEx (AND, l, r) ->
                BinEx (AND, opt l, opt r)
        | UnEx (NEG, l)     ->
                UnEx (NEG, opt l)
        | BinEx (OR, l, r) as e ->
                let res = list_to_binex OR (I.try_glue (collect_conjuncts [] e))
                in
                res

        | e -> e
    in
    let map_rule r = { r with Sk.guard = opt (Simplif.canonical r.Sk.guard) } in
    { sk with Sk.rules = List.map map_rule sk.Sk.rules }


let fuse skels new_name = 
    let first = match skels with
        | hd :: _ -> hd
        | [] -> raise (Failure "At least one skeleton is needed")
    in
    if List.exists (fun sk -> sk.Sk.shared <> first.Sk.shared) skels
    then raise (Failure ("Skeletons have different sets of shared variables"));
    if List.exists (fun sk -> sk.Sk.params <> first.Sk.params) skels
    then raise (Failure ("Skeletons have different sets of params variables"));
    let new_locals = List.fold_left (fun l sk -> l @ sk.Sk.locals) [] skels in

    let map_rule nlocs r =
        { r with Sk.src = nlocs + r.Sk.src; Sk.dst = nlocs + r.Sk.dst; }
    in
    let each_skel (nlocs, collected) sk =
        let new_rules = List.map (map_rule nlocs) sk.Sk.rules in
        (nlocs + sk.Sk.nlocs, collected @ new_rules )
    in
    let _, all_rules = List.fold_left each_skel (0, []) skels in

    let map_loc sk start len loc =
        let before = if start <= 0 then [] else BatList.make start (-1) in
        let after = if len <= 0 then [] else BatList.make len (-1) in
        before @ loc @ after
    in
    let each_loc (start, len, collected) sk =
        let nlocals = List.length sk.Sk.locals in
        let new_len = len - nlocals in
        let new_start = start + nlocals in
        let new_locs = List.map (map_loc sk start new_len) sk.Sk.locs in
        (new_start, new_len, collected @ new_locs)
    in
    let _, _, all_locs =
        List.fold_left each_loc (0, List.length new_locals, []) skels
    in
    let each_loc_var sk start map loc i =
        let v = IntMap.find i sk.Sk.loc_vars in
        let nv = v#copy (Sk.locname loc) in
        IntMap.add (start + i) nv map
    in
    let each_skel_loc_var (map, start) sk =
        let new_locs = Accums.list_sub all_locs start sk.Sk.nlocs in
        let map = 
            List.fold_left2 (each_loc_var sk start) map new_locs (range 0 sk.Sk.nlocs)
        in
        (map, start + sk.Sk.nlocs)
    in
    let all_loc_vars, _ =
        List.fold_left each_skel_loc_var (IntMap.empty, 0) skels
    in
    let add_to_map _ v map = IntMap.add v#id v map in
    let id_map = IntMap.fold add_to_map all_loc_vars IntMap.empty in
    let map_var v =
        if IntMap.mem v#id id_map
        then Var (IntMap.find v#id id_map)
        else Var v
    in
    let each_init (set, collected) e =
        let mapped_e = map_vars map_var e in
        let e_s = SpinIrImp.expr_s mapped_e in
        if StrSet.mem e_s set
        then (set, collected)
        else (StrSet.add e_s set, mapped_e :: collected)
    in
    let each_skel_init (set, collected) sk = 
        List.fold_left each_init (set, collected) sk.Sk.inits
    in
    let _, all_inits =
        List.fold_left each_skel_init (StrSet.empty, []) skels
    in
    let merge_two_forms name a b =
        match (a, b) with
        | Some _, Some _ ->
            raise (Failure ("Duplicate formula " ^ name))

        | Some f, _ -> Some f

        | _, b -> b
    in
    let merge_skel_forms forms sk =
        StrMap.merge merge_two_forms forms sk.Sk.forms
    in
    {
        Sk.name = new_name;
        Sk.nlocs = List.fold_left (fun s sk -> s + sk.Sk.nlocs) 0 skels;
        Sk.nrules = List.fold_left (fun s sk -> s + sk.Sk.nrules) 0 skels;
        Sk.locals = new_locals;
        Sk.locs = all_locs;
        Sk.rules = all_rules;
        Sk.inits = List.rev all_inits;
        Sk.loc_vars = all_loc_vars;
        Sk.shared = first.Sk.shared;
        Sk.params = first.Sk.params;
        Sk.assumes = List.concat (List.map (fun sk -> sk.Sk.assumes) skels);
        Sk.forms = List.fold_left merge_skel_forms StrMap.empty skels;
    }


(* the intermediate structure to successively construct Sk *)
module SkB = struct
    (** the builder's state *)
    type state_t = {
        loc_map: (Sk.loc_t, int) Hashtbl.t;
        skel: Sk.skel_t;
    }

    (** context for a function that constructs locations and rules *)
    type context_t = {
        sym_tab: symb_tab;
        type_tab: data_type_tab;
        prev_next: (var * var) list;
        state: state_t ref;
    }

    let empty locals shared params =
        { loc_map = Hashtbl.create 8;
          skel = Sk.empty locals shared params}

    let finish st name =
        let cmp_rules a b =
            if (a.Sk.src, a.Sk.dst) < (b.Sk.src, b.Sk.dst)
            then -1
            else if (a.Sk.src, a.Sk.dst) = (b.Sk.src, b.Sk.dst) then 0 else 1
        in

        { st.skel
            with Sk.name = name; 
                Sk.locs = List.rev st.skel.Sk.locs;
                Sk.rules = List.sort cmp_rules st.skel.Sk.rules;
                inits = st.skel.Sk.inits
        }

    (* get location index or allocate a new one *)
    let get_loci st loc =
        Hashtbl.find st.loc_map loc

    let intro_loc_vars st type_tab =
        let intro map loc =
            let nv = new_var (Sk.locname loc) in
            type_tab#set_type nv (new data_type SpinTypes.TUNSIGNED);
            IntMap.add (get_loci !st loc) nv map
        in
        let map =
            List.fold_left intro IntMap.empty (hashtbl_keys (!st).loc_map)
        in
        st := { !st with skel = { !st.skel with Sk.loc_vars = map }};
        IntMap.fold (fun _ v l -> v :: l) map []

    let add_loc st loc =
        try get_loci !st loc
        with Not_found ->
            let idx = !st.skel.Sk.nlocs in
            Hashtbl.replace !st.loc_map loc idx;
            st := { !st with skel = { !st.skel with Sk.nlocs = idx + 1;
                Sk.locs = loc :: !st.skel.Sk.locs }};
            idx

    let get_nlocs st =
        !st.skel.Sk.nlocs

    let add_rule st rule =
        try list_find_pos rule !st.skel.Sk.rules (* we don't have many rules *)
        with Not_found -> 
            let idx = !st.skel.Sk.nrules in
            st := { !st with skel = { !st.skel with Sk.nrules = idx + 1;
                Sk.rules = rule :: !st.skel.Sk.rules }};
            idx
            

    let add_init st init_expr =
        st := { !st with
            skel = { !st.skel with Sk.inits = init_expr :: !st.skel.Sk.inits }
        }

    let add_assume st assump =
        st := { !st with
            skel = { !st.skel with Sk.assumes = assump :: !st.skel.Sk.assumes }
        }
end


type builder_fun_t =
    SkB.context_t -> Spin.token SpinIr.expr
        -> (string, Spin.token SpinIr.expr) Hashtbl.t -> unit


let transition_to_rule builder path_cons vals (prev, next) =
    let assert_all_locals_eliminated e =
        let each v =
            if is_temp v && not (Hashtbl.mem vals v#get_name)
            then raise (Failure (sprintf "Can't eliminate local %s" v#get_name))
        in
        List.iter each (expr_used_vars e)
    in
    let load_prev h (x, i) =
        Hashtbl.replace h x#get_name (IntConst i)
    in
    let load_next h (x, i) =
        match Hashtbl.find vals x#get_name with
        | IntConst b -> ()
        | Var v ->
            if is_temp v
            (* this variable was introduced by havoc *)
            then Hashtbl.replace h v#get_name (IntConst i)
        (* TODO: replace the expression on rhs with IntConst a *)
        | _ -> raise (SymbExec_error "Complex expression in rhs")
    in
    let is_inconsistent h (x, value) =
        let rhs = Hashtbl.find vals x#get_name in
        let of_const = function
            | IntConst i -> i
            | _ -> raise (Failure "Expected a constant")
        in
        let val_fun = function
            | Var v ->
                begin
                    try of_const (Hashtbl.find h v#get_name)
                    with Not_found -> raise (Failure (v#get_name ^ " not found"))
                end
            | _ as e -> raise (Invalid_argument (SpinIrImp.expr_s e))
        in
        match SpinIrEval.eval_expr val_fun rhs with 
            (* the next value of the transition contradicts
               to the computed value *)
        | SpinIrEval.Int j -> j <> value
        | SpinIrEval.Bool _ -> raise (Failure ("Unexpected bool"))
    in
    let h = Hashtbl.create 10 in
    List.iter (load_prev h) prev;
    let npc = sub_vars h path_cons in
    let h = Hashtbl.create 10 in
    List.iter (load_next h) next;
    let npc = sub_vars h npc in

    (* tracing... *)
    let trace_print () =
        Printf.sprintf "tr %s -> %s\n"
            (str_join "." (List.map int_s (List.map snd prev)))
            (str_join "." (List.map int_s (List.map snd next)))
    in
    Debug.trace Trc.ssk trace_print;

    Debug.trace Trc.ssk
        (fun _ -> Printf.sprintf "npc:: %s\n" (SpinIrImp.expr_s npc));
    let trace_print k v =
        let p () = Printf.sprintf "%s <- %s\n" k (SpinIrImp.expr_s v) in
        Debug.trace Trc.ssk p
    in
    Hashtbl.iter trace_print vals;
    (* end of tracing *)

    assert_all_locals_eliminated npc;
    let h = Hashtbl.create 10 in
    List.iter (load_prev h) prev; List.iter (load_next h) next;
    let inconsistent = List.exists (is_inconsistent h) next in
    match npc, inconsistent with
    | IntConst 0, _ -> () (* the path conditions are violated *)
    | _, true -> ()    (* the state after the execution is invalid *)
    | _ -> (* o.k. *)
        Debug.trace Trc.ssk (fun _ -> "ADDED");
        let src = SkB.add_loc builder (List.map snd prev) in
        let dst = SkB.add_loc builder (List.map snd next) in
        let guard = npc in
        let to_asgn name rhs l =
            (* use NuSMV style: next(x) = x + 1 *)
            try let v = List.find (fun v -> v#get_name = name)
                    !builder.SkB.skel.Sk.shared in
                (BinEx (EQ, UnEx (NEXT, Var v), rhs)) :: l
            with Not_found -> l
        in
        let rule = { Sk.src = src; Sk.dst = dst; Sk.guard = guard;
            Sk.act = Hashtbl.fold to_asgn vals [] } in
        ignore (SkB.add_rule builder rule)


let reconstruct_rules trs ctx path_cons vals =
    Debug.trace Trc.ssk
        (fun _ -> Printf.sprintf "path_cons = %s\n" (SpinIrImp.expr_s path_cons));
    List.iter (transition_to_rule ctx.SkB.state path_cons vals) trs


let make_init rt prog proc locals builder =
    let reg_tab = (rt#caches#find_struc prog)#get_regions proc#get_name in
    let body = proc#get_stmts in
    let init_stmts = (reg_tab#get "decl" body) @ (reg_tab#get "init" body) in

    let to_loci eqs =
        let vals = List.map snd eqs in (* assignments to the locals *)
        SkB.add_loc builder vals
    in
    let locis = List.rev_map to_loci (SkelStruc.comp_seq locals init_stmts) in
    let loc_var i = Sk.locvar !builder.SkB.skel i in
    (* the counters that are initialized *)
    let init_sum =
        list_to_binex PLUS (List.map (fun i -> Var (loc_var i)) locis) in
    (* the counters that are initialized to zero *)
    let locisset =
        List.fold_left (fun s i -> IntSet.add i s) IntSet.empty locis in
    let zerolocs = List.filter
        (fun i -> not (IntSet.mem i locisset)) (range 0 (SkB.get_nlocs builder)) in
    (* the globals are assigned as by declarations *)
    let init_shared (v, e) =
        match e with
        | Nop _ -> BinEx (EQ, Var v, IntConst 0)
        | IntConst _ -> BinEx (EQ, Var v, e)
        | _ -> raise (Failure ("Unexpected initialization: " ^ (SpinIrImp.expr_s e)))
    in
    (* the resulting list of initialization expressions *)
    (BinEx (EQ, init_sum, proc#get_active_expr))
        :: (List.map (fun i -> BinEx (EQ, Var (loc_var i), IntConst 0)) zerolocs)
        @ (List.map init_shared (Program.get_shared_with_init prog))


let build_with builder_fun rt prog proc =
    (* do symbolic exploration/simplification *)
    (* collect a formula along the path *)
    let reg_tab = (rt#caches#find_struc prog)#get_regions proc#get_name in
    let all_stmts = SpinIrImp.mir_to_lir (reg_tab#get "comp" proc#get_stmts) in
    let loop_sig = SkelStruc.extract_loop_sig prog reg_tab proc in
    let prev_next = SkelStruc.get_prev_next loop_sig in

    let cfg = Cfg.remove_ineffective_blocks (mk_cfg all_stmts) in
    let shared = Program.get_shared prog in
    let params = Program.get_params prog in
    let all_vars = shared @ proc#get_locals in
    let primary_locals = List.map fst prev_next in
    let builder = ref (SkB.empty primary_locals shared params) in

    let tt = (Program.get_type_tab prog)#copy in
    let st = new symb_tab proc#get_name in
    (*
    st#add_all_symb (Program.get_sym_tab prog)#get_symbs;
    *)
    st#add_all_symb proc#get_symbs_rec;

    let ctx = { SkB.sym_tab = st; SkB.type_tab = tt;
        SkB.prev_next = prev_next; SkB.state = builder; }
    in

    (* collect initial conditions *)
    log INFO ("    enumerating symbolic paths of " ^ proc#get_name);
    let path_efun = enum_paths cfg in
    let num_paths =
        path_efun (exec_path rt#solver tt st all_vars (builder_fun ctx))
    in
    log INFO (sprintf "    enumerated %d symbolic paths in process %s"
                num_paths proc#get_name);

    (* collect initial conditions *)
    let ntt = (Program.get_type_tab prog)#copy in
    let loc_vars = SkB.intro_loc_vars builder ntt in
    let vr = rt#caches#analysis#get_var_roles prog in
    List.iter (fun v -> vr#add v VarRole.LocalUnbounded) loc_vars;

    let new_prog =
        (Program.set_shared (loc_vars @ shared)
            (Program.set_type_tab ntt prog)) in
    rt#caches#analysis#set_var_roles new_prog vr; (* req. by make_init *)
    
    let inits = make_init rt prog proc primary_locals builder in
    List.iter (SkB.add_init builder) inits;
    
    (* get the result *)
    let sk = SkB.finish !builder proc#get_name in
    { sk with Sk.assumes = Program.get_assumes prog }


let state_pairs_to_rules rt prog proc trs =
    build_with (reconstruct_rules trs) rt prog proc


(**
 Expand quantifiers to conditions over location counters.
 This function works only when an expression contains no shared variables,
 nor parameters. Use expand_quant_with_shared in the latter case.
 *)
let expand_quant prog sk ~quant e =
    let var_names = List.map (fun v -> v#get_name) sk.Sk.locals in
    let is_matching_loc loc_no =
        let lookup = List.combine var_names (Sk.loc_by_no sk loc_no) in
        let val_fun = function
            | Var v ->
            begin
                try List.assoc v#get_name lookup
                with Not_found ->
                    raise (Failure (Printf.sprintf "Var %s not found" v#get_name))
            end

            | e ->
                raise (Failure ("val_fun(%s) is undefined" ^ (SpinIrImp.expr_s e)))
        in
        (* QAll needs negation *)
        (SpinIrEval.Bool (quant <> QAll)) = SpinIrEval.eval_expr val_fun e
    in
    let matching = List.filter is_matching_loc (range 0 sk.Sk.nlocs) in
    let each_loc accum l =
        match quant with
        | QExist -> (* there is a non-zero location *)
            let cmp =
                BinEx (NE, Var (Sk.locvar sk l), IntConst 0) in
            if is_nop accum then cmp else BinEx (OR, cmp, accum)

        | QAll -> (* forall: all other locations are zero *)
            let cmp =
                BinEx (EQ, Var (Sk.locvar sk l), IntConst 0) in
            if is_nop accum then cmp else BinEx (AND, cmp, accum)

        | QCard ->
            if is_nop accum
            then Var (Sk.locvar sk l)
            else BinEx (PLUS, Var (Sk.locvar sk l), accum)
    in
    List.fold_left each_loc (Nop "") matching


(**
 Expand quantifiers to conditions over location counters.
 As opposite to expand_quant, this function works only
 with shared variables and parameters.
 *)
let expand_quant_with_shared prog skels ~quant e =
    let pname = Ltl.find_proc_name ~err_not_found:true e in
    let sk =
        try List.find (fun sk -> sk.Sk.name = pname) skels
        with Not_found -> raise (Failure ("No skeleton " ^ pname))
    in
    let add s v = StrSet.add v#get_name s in
    let local_set = List.fold_left add StrSet.empty sk.Sk.locals in
    let expand_if cond e =
        if not cond then e else expand_quant prog sk ~quant:quant e
    in
    (* find the topmost expressions that contain only local variables
       and expand the quantifier for them
     *)
    let rec find_and_replace = function
    | IntConst i ->
        (true, IntConst i)

    | Var v ->
        let is_local = StrSet.mem v#get_name local_set in
        (is_local, Var v)

    | UnEx (op, e) ->
        let (is_local, ne) = find_and_replace e in
        (is_local, UnEx (op, ne))

    | BinEx (IMPLIES as op, l, r)
    | BinEx (OR as op, l, r)
    | BinEx (AND as op, l, r) ->
        let (is_local_l, nl) = find_and_replace l in
        let (is_local_r, nr) = find_and_replace r in
        if is_local_l && is_local_r
        then (true, BinEx (op, nl, nr))
        else (false, BinEx (op, expand_if is_local_l nl, expand_if is_local_r nr))

    | BinEx (op, l, r) ->
        let (is_local_l, nl) = find_and_replace l in
        let (is_local_r, nr) = find_and_replace r in
        (is_local_l && is_local_r, BinEx (op, nl, nr))

    | _ as e -> (true, e)
    in
    let is_local, ne = find_and_replace e in
    expand_if is_local ne


(** expand quantifiers in the propositional symbols *)
let expand_props_in_ltl prog skels prop_form =
    let atomics = Program.get_atomics_map prog in
    let tt = Program.get_type_tab prog in
    let rec expand_card = function
        | UnEx (CARD, r) ->
            expand_quant_with_shared prog skels ~quant:QCard r

        | UnEx (t, r) ->
                UnEx (t, expand_card r)

        | BinEx (t, l, r) ->
                BinEx (t, expand_card l, expand_card r)

        | e -> e
    in
    let rec pr_atomic = function
        | PropGlob e ->
            expand_card e

        | PropAll e ->
            expand_quant_with_shared prog skels ~quant:QAll e

        | PropSome e ->
            expand_quant_with_shared prog skels ~quant:QExist e

        | PropAnd (l, r) ->
            BinEx (AND, pr_atomic l, pr_atomic r)

        | PropOr (l, r) ->
            BinEx (OR, pr_atomic l, pr_atomic r)
    in
    let rec pr neg = function
    | BinEx (AND as t, l, r)

    | BinEx (OR as t, l, r) ->
        let op, nop = if t = AND then AND, OR else OR, AND in
        BinEx ((if neg then nop else op), pr neg l, pr neg r)

    | UnEx (NEG, r) ->
        pr (not neg) r

    | Var v ->
        let find n =
            try StrMap.find v#get_name atomics
            with Not_found ->
                raise (Failure
                    (sprintf "Atomic proposition %s not found" v#get_name))
        in
        let e =
            if (tt#get_type v)#basetype = SpinTypes.TPROPOSITION
            then pr_atomic (find v#get_name)
            else Var v
        in
        if neg then UnEx (NEG, e) else e

    | UnEx (t, l) ->
        let ne =
            if neg
            then UnEx (NEG, UnEx (t, UnEx (NEG, pr neg l)))
            else UnEx (t, pr false l) in
        Ltl.normalize_form ne (* remove redundant negations *)

    | BinEx (t, l, r) ->
        let nl = if neg then UnEx (NEG, pr neg l) else pr neg l in
        let nr = if neg then UnEx (NEG, pr neg r) else pr neg r in
        let ne = BinEx (t, nl, nr) in
        let ne = if neg then UnEx (NEG, ne) else ne in
        Ltl.normalize_form ne (* remove redundant negations *)

    | e ->
        let ne = if neg then UnEx (NEG, e) else e in
        Ltl.normalize_form ne
    in
    pr false prop_form


(* expand propositions in LTL formulas *)
let expand_props_in_ltl_forms prog skels ltl_forms =
    StrMap.map (expand_props_in_ltl prog skels) ltl_forms

