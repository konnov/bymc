(* Extract a symbolic skeleton.
 *
 * Igor Konnov, 2014
 *)

open Printf

open Accums
open Spin
open SpinIr
open SpinIrImp
open SymbExec

open Cfg
open Ssa

(* the symbolic skeleton *)
module Sk = struct
    type rule_t = {
        src: int; dst: int;
        guard: token expr; act: token expr list
    }
    
    type loc_t = int list (* variable assignments *)

    type skel_t = {
        name: string; (* just a name *)
        nlocs: int; (* the number of locations *)
        locs: loc_t list; (* the list of locations *)
        locals: var list; (* the local variables *)
        shared: var list; (* the shared variables *)
        nrules: int; (* the number of rules *)
        rules: rule_t list; (* the rules *)
    }

    let empty locals shared =
        { name = ""; nlocs = 0; locs = [];
          locals = locals; shared = shared;
          nrules = 0; rules = [] }

    let print out sk =
        fprintf out "skel %s {\n" sk.name;
        fprintf out "  locals %s;\n"
            (str_join ", " (List.map (fun v -> v#get_name) sk.locals));
        fprintf out "  shared %s;\n"
            (str_join ", " (List.map (fun v -> v#get_name) sk.shared));
        let ploc (i, l) =
            fprintf out "    loc%d: [%s];\n" i (str_join "; " (List.map int_s l))
        in
        fprintf out "  locations (%d) {\n" sk.nlocs;
        List.iter ploc (lst_enum sk.locs);
        fprintf out "  }\n\n";
        let prule (i, r) =
            fprintf out "  %d: loc%d -> loc%d\n      when (%s)\n      do { %s };\n"
                i r.src r.dst (expr_s r.guard)
                (str_join "; " (List.map expr_s r.act))
        in
        fprintf out "  rules (%d) {:\n" sk.nrules;
        List.iter prule (lst_enum sk.rules);
        fprintf out "  }\n";
        fprintf out "} /* %s */\n" sk.name

end


(* the intermediate structure to successively construct Sk *)
module SkB = struct
    type state_t = {
        loc_map: (Sk.loc_t, int) Hashtbl.t;
        skel: Sk.skel_t;
    }

    let empty locals shared =
        { loc_map = Hashtbl.create 8; skel = Sk.empty locals shared }

    let finish st name =
        { st.skel
            with Sk.name = name; 
                Sk.locs = List.rev st.skel.Sk.locs;
                Sk.rules = List.rev st.skel.Sk.rules;
        }

    (* get location index or allocate a new one *)
    let get_loci st loc =
        Hashtbl.find st.loc_map loc

    let add_loc st loc =
        try get_loci !st loc
        with Not_found ->
            let idx = !st.skel.Sk.nlocs in
            Hashtbl.replace !st.loc_map loc idx;
            st := { !st with skel = { !st.skel with Sk.nlocs = idx + 1;
                Sk.locs = loc :: !st.skel.Sk.locs }};
            idx

    let add_rule st rule =
        let idx = !st.skel.Sk.nrules in
        st := { !st with skel = { !st.skel with Sk.nrules = idx + 1;
            Sk.rules = rule :: !st.skel.Sk.rules }};
        idx
            
end


let label_transition builder path_cons vals (prev, next) =
    let load_prev h (x, i) =
        Hashtbl.replace h x#get_name (Const i)
    in
    let load_next h (x, i) =
        match Hashtbl.find vals x#get_name with
        | Const b -> ()
        | Var v -> (* this variable was introduced by havoc *)
            Hashtbl.replace h v#get_name (Const i)
        (* TODO: replace the expression on rhs with Const a *)
        | _ -> raise (SymbExec_error "Complex expression in rhs")
    in
    let is_inconsistent (x, i) =
        match Hashtbl.find vals x#get_name with
            (* the next value of the transition contradicts
               to the computed value *)
        | Const j -> j <> i
        | _ -> false
    in
    let h = Hashtbl.create 10 in
    List.iter (load_prev h) prev;
    let npc = sub_vars h path_cons in
    let h = Hashtbl.create 10 in
    List.iter (load_next h) next;
    let npc = sub_vars h npc in
    let inconsistent = List.exists is_inconsistent next in
    match npc, inconsistent with
    | Const 0, _ -> () (* the path conditions are violated *)
    | _, true -> ()    (* the state after the execution is invalid *)
    | _ -> (* o.k. *)
        let src = SkB.add_loc builder (List.map snd prev) in
        let dst = SkB.add_loc builder (List.map snd next) in
        let guard = npc in
        let to_asgn name rhs l =
            try let v = List.find (fun v -> v#get_name = name)
                    !builder.SkB.skel.Sk.shared in
                (BinEx (ASGN, Var v, rhs)) :: l
            with Not_found -> l
        in
        let rule = { Sk.src = src; Sk.dst = dst; Sk.guard = guard;
            Sk.act = Hashtbl.fold to_asgn vals [] } in
        ignore (SkB.add_rule builder rule)


let propagate builder trs path_cons vals =
    List.iter (label_transition builder path_cons vals) trs


let collect_constraints rt prog proc primary_vars trs =
    (* do symbolic exploration/simplification *)
    (* collect a formula along the path *)
    let get_comp p =
        let reg_tab =
            (rt#caches#find_struc prog)#get_regions p#get_name in
        reg_tab#get "comp" p#get_stmts 
    in
    let all_stmts = mir_to_lir (get_comp proc) in
    let cfg = Cfg.remove_ineffective_blocks (mk_cfg all_stmts) in
    let ntt = (Program.get_type_tab prog)#copy in
    let nst = new symb_tab proc#get_name in
    nst#add_all_symb proc#get_symbs;
    let shared = Program.get_shared prog in
    let all_vars = shared @ proc#get_locals in
    let builder = ref (SkB.empty primary_vars shared) in

    let path_efun = enum_paths cfg in
    let num_paths =
        path_efun (exec_path rt#solver ntt nst all_vars (propagate builder trs))
    in
    Printf.printf "    enumerated %d paths\n\n" num_paths;
    
    let sk = SkB.finish !builder proc#get_name in
    sk

