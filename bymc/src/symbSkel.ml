(* Extract a symbolic skeleton.
 *
 * Igor Konnov, 2014
 *)

open Printf

open Accums
open Spin
open SpinIr
open SymbExec

open Cfg
open Ssa

(* the symbolic skeleton *)
module Sk = struct
    type rule_t = {
        src: int; dst: int; (* indices in locs *)
        guard: token expr; act: token expr list
    }
    
    type loc_t = int list (* variable assignments *)

    type skel_t = {
        name: string; (* just a name *)
        nlocs: int; (* the number of locations *)
        locs: loc_t list; (* the list of locations *)
        locals: var list; (* local variables *)
        shared: var list; (* shared variables *)
        params: var list; (* parameters *)
        nrules: int; (* the number of rules *)
        rules: rule_t list; (* the rules *)
        inits: token expr list; (* initialization expressions *)
    }

    let empty locals shared params =
        { name = ""; nlocs = 0; locs = [];
          locals = locals; shared = shared; params = params;
          nrules = 0; rules = []; inits = [] }

    let locname l =
        sprintf "loc%s" (str_join "_" (List.map int_s l))

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
        fprintf out "skel %s {\n" sk.name;
        let vname v = v#get_name in
        fprintf out "  local %s;\n"
            (str_join ", " (List.map vname sk.locals));
        fprintf out "  shared %s;\n"
            (str_join ", " (List.map vname sk.shared));
        fprintf out "  parameters %s;\n"
            (str_join ", " (List.map vname sk.params));
        let ploc (i, l) =
            fprintf out "    %s: [%s];\n"
                (locname l) (str_join "; " (List.map int_s l))
        in
        fprintf out "  locations (%d) {\n" sk.nlocs;
        List.iter ploc (lst_enum sk.locs);
        fprintf out "  }\n\n";
        fprintf out "  inits (%d) {\n" (List.length sk.inits);
        let pinit e = fprintf out "    %s;\n" (expr_s e) in
        List.iter pinit sk.inits;
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
        fprintf out "} /* %s */\n" sk.name

    let to_file name sk =
        let f = open_out name in
        print f sk;
        close_out f
end


(* the intermediate structure to successively construct Sk *)
module SkB = struct
    type state_t = {
        loc_map: (Sk.loc_t, int) Hashtbl.t;
        skel: Sk.skel_t;
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
            type_tab#set_type nv (new data_type SpinTypes.TINT);
            IntMap.add (get_loci !st loc) nv map
        in
        let map = List.fold_left intro IntMap.empty (hashtbl_keys (!st).loc_map)
        in
        map, IntMap.fold (fun _ v l -> v :: l) map []

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
end


let label_transition builder path_cons vals (prev, next) =
    let assert_all_locals_eliminated e =
        let each v =
            if String.contains v#get_name '$'
                && not (Hashtbl.mem vals v#get_name)
            then raise (Failure (sprintf "Can't eliminate local %s" v#get_name))
        in
        List.iter each (expr_used_vars e)
    in
    let load_prev h (x, i) =
        Hashtbl.replace h x#get_name (Const i)
    in
    let load_next h (x, i) =
        match Hashtbl.find vals x#get_name with
        | Const b -> ()
        | Var v ->
            if String.contains v#get_name '$'
            (* this variable was introduced by havoc *)
            then Hashtbl.replace h v#get_name (Const i)
        (* TODO: replace the expression on rhs with Const a *)
        | _ -> raise (SymbExec_error "Complex expression in rhs")
    in
    let is_inconsistent h (x, value) =
        let rhs = Hashtbl.find vals x#get_name in
        let of_const = function
            | Const i -> i
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
    Debug.trace Trc.syx trace_print;

    Debug.trace Trc.syx
        (fun _ -> Printf.sprintf "npc:: %s\n" (SpinIrImp.expr_s npc));
    let trace_print k v =
        let p () = Printf.sprintf "%s <- %s\n" k (SpinIrImp.expr_s v) in
        Debug.trace Trc.syx p
    in
    Hashtbl.iter trace_print vals;
    (* end of tracing *)

    assert_all_locals_eliminated npc;
    let h = Hashtbl.create 10 in
    List.iter (load_prev h) prev; List.iter (load_next h) next;
    let inconsistent = List.exists (is_inconsistent h) next in
    match npc, inconsistent with
    | Const 0, _ -> () (* the path conditions are violated *)
    | _, true -> ()    (* the state after the execution is invalid *)
    | _ -> (* o.k. *)
        Debug.trace Trc.syx (fun _ -> "ADDED");
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


let propagate builder trs path_cons vals =
    Debug.trace Trc.syx
        (fun _ -> Printf.sprintf "path_cons = %s\n" (SpinIrImp.expr_s path_cons));
    List.iter (label_transition builder path_cons vals) trs


let make_init rt prog proc locals loc_map builder =
    let reg_tab = (rt#caches#find_struc prog)#get_regions proc#get_name in
    let body = proc#get_stmts in
    let init_stmts = (reg_tab#get "decl" body) @ (reg_tab#get "init" body) in
    let to_loci eqs =
        let vals = List.map snd eqs in (* assignments to the locals *)
        SkB.get_loci !builder vals
    in
    let locis = List.map to_loci (SkelStruc.comp_seq locals init_stmts) in
    let loc_var i = IntMap.find i loc_map in
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
        | Nop _ -> BinEx (EQ, Var v, Const 0)
        | Const _ -> BinEx (EQ, Var v, e)
        | _ -> raise (Failure ("Unexpected initialization: " ^ (SpinIrImp.expr_s e)))
    in
    (* the resulting list of initialization expressions *)
    (BinEx (EQ, init_sum, proc#get_active_expr))
        :: (List.map (fun i -> BinEx (EQ, Var (loc_var i), Const 0)) zerolocs)
        @ (List.map init_shared (Program.get_shared_with_init prog))
            


let collect_constraints rt prog proc primary_vars trs =
    (* do symbolic exploration/simplification *)
    (* collect a formula along the path *)
    let get_comp p =
        let reg_tab = (rt#caches#find_struc prog)#get_regions p#get_name in
        reg_tab#get "comp" p#get_stmts 
    in
    let all_stmts = SpinIrImp.mir_to_lir (get_comp proc) in
    let cfg = Cfg.remove_ineffective_blocks (mk_cfg all_stmts) in
    let shared = Program.get_shared prog in
    let params = Program.get_params prog in
    let all_vars = shared @ proc#get_locals in
    let builder = ref (SkB.empty primary_vars shared params) in

    (* collect steps expressed via paths *)
    let tt = (Program.get_type_tab prog)#copy in
    let st = new symb_tab proc#get_name in
    st#add_all_symb proc#get_symbs;
    let path_efun = enum_paths cfg in
    let num_paths =
        path_efun (exec_path rt#solver tt st all_vars (propagate builder trs))
    in
    Printf.printf "    enumerated %d paths\n\n" num_paths;

    (* collect initial conditions *)
    let ntt = (Program.get_type_tab prog)#copy in
    let loc_map, loc_vars = SkB.intro_loc_vars builder ntt in
    let vr = rt#caches#analysis#get_var_roles prog in
    List.iter (fun v -> vr#add v VarRole.LocalUnbounded) loc_vars;
    rt#caches#analysis#set_var_roles prog vr;
    let inits = make_init rt prog proc primary_vars loc_map builder in
    List.iter (SkB.add_init builder) inits;

    let new_prog =
        (Program.set_shared (loc_vars @ shared)
            (Program.set_type_tab ntt prog)) in
    
    (* get the result *)
    let sk = SkB.finish !builder proc#get_name in
    sk, new_prog

