(*
 Translating processes in SSA and encoding them in NuSMV format.
 This is the third try to create an efficient encoding in NuSMV.
 *)

open Printf

open Accums
open Cfg
open CfgSmt
open Nusmv
open Simplif
open Spin
open SpinIr
open SpinIrImp
open Ssa

exception NusmvEncoding_error of string

(* ============================= utility declarations and functions *)

type proc_var_t =
    | SharedIn of var * data_type
    | SharedOut of var * data_type
    | LocalIn of var * data_type
    | LocalOut of var * data_type
    | Temp of var * data_type

let proc_var_lt a b =
    match a, b with
    | (SharedIn _, SharedOut _)
    | (SharedIn _, LocalIn _)
    | (SharedIn _, LocalOut _)
    | (SharedIn _, Temp _)
    | (SharedOut _, LocalIn _)
    | (SharedOut _, LocalOut _)
    | (SharedOut _, Temp _)
    | (LocalIn _, LocalOut _)
    | (LocalIn _, Temp _)
    | (LocalOut _, Temp _) -> true
    | (SharedIn (v, _), SharedIn (w, _))
    | (SharedOut (v, _), SharedOut (w, _))
    | (LocalIn (v, _), LocalIn (w, _))
    | (LocalOut (v, _), LocalOut (w, _))
    | (Temp (v, _), Temp (w, _)) ->
            (String.compare v#qual_name w#qual_name) < 0
    | _ -> false

let proc_var_cmp a b =
    if proc_var_lt a b
    then -1
    else if proc_var_lt b a
    then 1
    else 0


let is_var_temp = function
    | Temp _ -> true
    | _ -> false

let is_var_local = function
    | LocalIn _ -> true
    | LocalOut _ -> true
    | _ -> false

let is_var_shared_in = function
    | SharedIn _ -> true
    | _ -> false

let ptov = function
    | SharedIn (v, _)
    | SharedOut (v, _)
    | LocalIn (v, _)
    | LocalOut (v, _)
    | Temp (v, _) -> v

let ptovt = function
    | SharedIn (v, t)
    | SharedOut (v, t)
    | LocalIn (v, t)
    | LocalOut (v, t)
    | Temp (v, t) -> v, t


let strip_in s = String.sub s 0 ((String.length s) - 3 (* _IN *))
let strip_out s = String.sub s 0 ((String.length s) - 4 (* _OUT *))


let partition_var tt v =
    let is_in = (Str.last_chars v#get_name 3) = "_IN" in
    let is_out = (Str.last_chars v#get_name 4) = "_OUT" in
    let t = tt#get_type v in
    match (is_in, is_out) with
    | (true, _) ->
            if v#proc_name = "" then SharedIn (v, t) else LocalIn (v, t)
    | (_, true) ->
            if v#proc_name = "" then SharedOut (v, t) else LocalOut (v, t)
    | _ -> Temp (v, t)


let replace_with_next syms tt v =
    match partition_var tt v with
    | SharedOut (_, _) ->
        let inm = (strip_out v#get_name) ^ "_IN" in
        UnEx (NEXT, Var ((syms#lookup inm)#as_var))

    | _ -> Var v 

let vars_of_syms syms =
    let is_var s = s#get_sym_type = SymVar in
    List.map (fun s -> s#as_var) (List.filter is_var syms)


(* ====================== important functions *)

let module_of_proc rt prog proc =
    let to_ssa =
        let reg_tbl =
            (rt#caches#find_struc prog)#get_regions proc#get_name in
        let comp = reg_tbl#get "comp" proc#get_stmts in
        (* both locals and shared are the parameters of our module *)
        let locals = vars_of_syms proc#get_symbs in
        let shared = Program.get_shared prog in
        (* construct SSA as in SmtXducerPass *)
        let new_sym_tab = new symb_tab "tmp" in
        let new_type_tab = (Program.get_type_tab prog)#copy in
        let cfg = Cfg.remove_ineffective_blocks (mk_cfg (mir_to_lir comp)) in
        let cfg_ssa =
            mk_ssa false (shared @ locals) []
                new_sym_tab new_type_tab cfg in
        Cfg.write_dot (sprintf "ssa-comp-%s.dot" proc#get_name) cfg_ssa;
        let exprs =
            cfg_to_constraints proc#get_name new_sym_tab new_type_tab cfg_ssa
        in
        (new_type_tab, new_sym_tab, List.map expr_of_m_stmt exprs)
    in
    let ntt, syms, exprs = to_ssa in
    let new_vars = vars_of_syms syms#get_symbs in
    let exprs = List.map (map_vars (replace_with_next syms ntt)) exprs in
    let pvars = List.sort proc_var_cmp (List.map (partition_var ntt) new_vars) in
    let temps = List.filter is_var_temp pvars in
    let args =
        List.filter (fun pv -> is_var_local pv || is_var_shared_in pv) pvars in
    (* activate the process *)
    (* XXX: TODO: it does not work for several proctypes *)
    let invar = Var ((syms#lookup "at_0")#as_var) in
    let mod_type =
        SModule (proc#get_name,
            List.map ptov args,
            [SVar (List.map ptovt temps); SInvar [invar]; STrans exprs])
    in
    (mod_type, args)


let create_proc_mods rt intabs_prog =
    let transform_proc (globals, main_sects) p =
        let mod_type, args = module_of_proc rt intabs_prog p in
        let to_param = function
            | SharedIn (v, t) -> (v#copy (strip_in v#get_name), t)
            | SharedOut (v, t) -> (v#copy (strip_out v#get_name), t)
            | LocalIn (v, t) -> raise (Failure ("Unexpected LocalIn"))
            | LocalOut (v, t) -> (v#copy (strip_out v#get_name), t)
            | _ -> raise (Failure ("Unexpected param type"))
        in
        let params = List.map to_param args in
        let inst = SModInst("p_" ^ p#get_name, p#get_name,
            (List.map (fun (v, _) -> Var v) params))
        in
        let locals = List.filter (fun (v, _) -> v#proc_name <> "") params in
        (mod_type :: globals, (SVar locals) :: inst :: main_sects)
    in
    let procs = Program.get_procs intabs_prog in
    let tt = Program.get_type_tab intabs_prog in
    let globals, main_sects = List.fold_left transform_proc ([], []) procs in
    let shared =
        List.map (fun v -> (v, tt#get_type v)) (Program.get_shared intabs_prog)
    in
    ((SVar shared) :: main_sects, globals)


(* partially copied from nusmvCounterClusterPass *)
(* TODO: deal with many process types *)
let module_of_counter rt ctrabs_prog p =
    let ctr_ctx = rt#caches#analysis#get_pia_ctr_ctx_tbl#get_ctx p#get_name in
    let dom = rt#caches#analysis#get_pia_dom in
    let tt = Program.get_type_tab ctrabs_prog in
    let dec_tbl =
        NusmvCounterClusterPass.collect_rhs rt#solver tt dom ctr_ctx PLUS in
    let inc_tbl =
        NusmvCounterClusterPass.collect_rhs rt#solver tt dom ctr_ctx MINUS in
    let prev_locals = List.map fst ctr_ctx#prev_next_pairs in
    let next_locals = List.map snd ctr_ctx#prev_next_pairs in
    let my_var v = v#copy ("my_" ^ v#get_name) in
    let cmp_idx join cmp vars =
        let f pv v = BinEx (cmp, Var v, Var (my_var pv)) in
        list_to_binex join (List.map2 f prev_locals vars)
    in
    let prev_eq = cmp_idx AND EQ prev_locals in
    let prev_ne = cmp_idx OR NE prev_locals in
    let next_eq = cmp_idx AND EQ next_locals in
    let next_ne = cmp_idx OR NE next_locals in
    let myval = new_var "myval" in
    let mk_case prev_ex next_ex prev_val next_vals =
        let guard = BinEx (AND, BinEx (AND, prev_ex, next_ex),
                                BinEx (EQ, Var myval, Const prev_val)) in
        let rhs = List.map (fun i -> Const i) next_vals in
        (guard, rhs)
    in
    let prev_cases = hashtbl_map (mk_case prev_eq next_ne) dec_tbl in
    let next_cases = hashtbl_map (mk_case prev_ne next_eq) inc_tbl in
    let cases = prev_cases @ next_cases @
        [(Var nusmv_true, [Var myval])] in
    let choice = SAssign [ANext (myval, cases)] in
    let args =
        myval :: (List.map my_var prev_locals)
            @ prev_locals @ next_locals
    in 
    SModule ("Counter" ^ p#get_name, args, [choice])


(* it is probably not the best way to do initialization *)
let init_of_ctrabs rt intabs_prog ctrabs_prog =
    let dom = rt#caches#analysis#get_pia_dom in
    let to_ssa l p =
        (* similar to AbsCounter.ctr_funcs#mk_init *)
        let ctr_ctx =
            rt#caches#analysis#get_pia_ctr_ctx_tbl#get_ctx p#get_name in
        let ctr = ctr_ctx#get_ctr in
        let reg_tab =
            (rt#caches#find_struc intabs_prog)#get_regions p#get_name in
        let init = reg_tab#get "init" p#get_stmts in
        let decl = reg_tab#get "decl" p#get_stmts in
        let init_vals =
            AbsCounter.find_init_local_vals ctr_ctx decl init in
        let size_dist_list =
            dom#scatter_abs_vals
                rt#solver p#get_active_expr (List.length init_vals) in
        let mk_opt (hits, l) local_vals abs_size =
            let valuation = Hashtbl.create 10 in
            let add_var (var, i) = Hashtbl.add valuation var i in
            List.iter add_var local_vals;
            let idx = ctr_ctx#pack_to_const valuation in
            let eq =
                BinEx (EQ,
                    Var (ctr#copy (sprintf "%s_%dI" ctr#get_name idx)),
                    Const abs_size) in
            (IntSet.add idx hits, eq :: l)
        in
        let mk_one_vec d =
            let e = IntSet.empty in
            let hits, ess = List.fold_left2 mk_opt (e, []) init_vals d in
            let zero l i =
                if not (IntSet.mem i hits)
                then BinEx (EQ,
                    Var (ctr#copy (sprintf "%s_%dI" ctr#get_name i)),
                    Const 0) :: l
                else l
            in
            let ess = List.fold_left zero ess (range 0 ctr_ctx#get_ctr_dim) in
            list_to_binex AND ess
        in
        let ex = list_to_binex OR (List.map mk_one_vec size_dist_list)
        in
        ex :: l
    in
    let bymc_loc = new_var "bymc_loc" in
    let init_global i v = BinEx (EQ, Var v, Const i) in
    let init_ess =
        (init_global 1 bymc_loc)
        :: (List.map (init_global 0) (Program.get_shared intabs_prog))
        @  List.fold_left to_ssa [] (Program.get_procs intabs_prog) in
    let bymc_loc_decl =
        let t = new data_type SpinTypes.TINT in
        t#set_range 0 2;
        SVar [(bymc_loc, t)]
    in
    let change_loc =
        ANext (bymc_loc, [(Var nusmv_true, [ Const 1 ])]) 
    in
    [ bymc_loc_decl; SInit init_ess; SAssign [change_loc] ]
    


let create_counter_mods rt ctrabs_prog =
    let dom = rt#caches#analysis#get_pia_dom in
    let create_vars l p =
        let ctr_ctx =
            rt#caches#analysis#get_pia_ctr_ctx_tbl#get_ctx p#get_name in
        let prev = List.map fst ctr_ctx#prev_next_pairs in
        let next = List.map snd ctr_ctx#prev_next_pairs in
        let ctr = ctr_ctx#get_ctr in
        let tp = new data_type SpinTypes.TINT in
        tp#set_range 0 dom#length;
        let per_idx l idx =
            let myctr = ctr#copy (sprintf "%s_%dI" ctr#get_name idx) in
            let valtab = ctr_ctx#unpack_from_const idx in
            let get_val v = Const (Hashtbl.find valtab v) in
            let tov v = Var v in
            let params =
                [tov myctr] @ (List.map get_val prev)
                @ (List.map tov prev) @ (List.map tov next) in
            let ne v = BinEx (NE, Var v, get_val v) in
            let invar =
                SInvar ([BinEx (OR,
                    BinEx (NE, Var myctr, Const 0),
                    list_to_binex OR (List.map ne prev))])
            in
            (SVar [(myctr, tp)])
                :: (SModInst( (sprintf "p_%s_%dI" ctr#get_name idx),
                         "Counter" ^ p#get_name, params))
                :: invar
                :: l
        in
        List.fold_left per_idx
            l (ctr_ctx#all_indices_for (fun _ -> true))
    in
    let procs = Program.get_procs ctrabs_prog in
    let main_sects = List.fold_left create_vars [] procs in
    let mods = List.map (module_of_counter rt ctrabs_prog) procs in
    (main_sects, mods)


let create_counter_specs rt ctrabs_prog =
    let type_tab = Program.get_type_tab ctrabs_prog in
    let atomics = Program.get_atomics_map ctrabs_prog in
    let create_spec sym_tab name ltl_form lst =
        let embedded = Ltl.embed_atomics type_tab atomics ltl_form in
        let flat = SymbExec.elim_array_access sym_tab embedded in
        let hidden_masked = Simplif.compute_consts flat in
        if not (Ltl.is_fairness_form name)
        then begin
            match hidden_masked with
            | UnEx (ALWAYS, f) as tf ->
                if Ltl.is_propositional type_tab f
                then (* use a faster algorithm *)
                    (SInvarSpec (name, f)) :: lst
                else (SLtlSpec (name, tf)) :: lst

            | _ as tf ->
                (SLtlSpec (name, tf)) :: lst
        end else begin
            let collect l = function
            | UnEx (ALWAYS, UnEx (EVENTUALLY, f)) as ff ->
                if Ltl.is_propositional type_tab f
                then (SJustice f) :: l
                else raise (NusmvEncoding_error
                    ("Unsupported fairness: " ^ (expr_s ff)))

            | _ as ff ->
                printf "WARN: unsupported fairness type (ignored): %s\n"
                    (expr_s ff);
                l
            in
            let tab = Hashtbl.create 1 in
            Hashtbl.add tab name hidden_masked;
            List.fold_left collect lst (Ltl.collect_fairness_forms tab)
        end
    in
    let create_reach lst p =
        let ctr_ctx = rt#caches#analysis#get_pia_ctr_ctx_tbl#get_ctx p#get_name
        in
        let ctr = ctr_ctx#get_ctr in
        let idx_spec l idx = 
            let myctr = ctr#copy (sprintf "%s_%dI" ctr#get_name idx) in
            let name = sprintf "r_%s%d" ctr#get_name idx in
            (SInvarSpec (name, BinEx (EQ, Var myctr, Const 0))) :: l
        in
        List.fold_left idx_spec lst (ctr_ctx#all_indices_for (fun _ -> true))
    in
    let reach_specs =
        List.fold_left create_reach [] (Program.get_procs ctrabs_prog)
    in
    let sym_tab = new symb_tab "tmp" in
    let reg_ctr p =
        let ctr_ctx =
            rt#caches#analysis#get_pia_ctr_ctx_tbl#get_ctx p#get_name in
        let ctr = ctr_ctx#get_ctr in
        let per_idx i =
            let v = ctr#copy (sprintf "%s_%dI" ctr#get_name i) in
            sym_tab#add_symb v#get_name (v :> symb)
        in
        List.iter per_idx (ctr_ctx#all_indices_for (fun _ -> true))
    in
    List.iter reg_ctr (Program.get_procs ctrabs_prog);
    let specs =
        Accums.StringMap.fold
            (create_spec sym_tab) (Program.get_ltl_forms ctrabs_prog) []
    in
    specs @ reach_specs


let collect_globals main_sect =
    let f lst = function
    | SVar decls -> (List.fold_left (fun  l (v, _) -> v :: l) lst decls)
    | _ -> lst
    in
    List.fold_left f [] main_sect


let hide_vars names sections =
    let is_vis n = not (StrSet.mem n names)
    in
    let rec rewrite_ex = function
    | Var v as e ->
        if is_vis v#mangled_name
        then e
        else Var nusmv_false  (* unreachable meaning always 0 *)

    | BinEx (EQ, Var v, Const i) as e ->
        if is_vis v#mangled_name
        then e
        (* unreachable meaning always 0 *)
        else if i > 0 then Var nusmv_false else Var nusmv_true

    | BinEx (NE, Var v, Const i) as e ->
        if is_vis v#mangled_name
        then e
        (* unreachable, always 0 *)
        else if i > 0 then Var nusmv_true else Var nusmv_false

    | BinEx (t, l, r) -> BinEx (t, rewrite_ex l, rewrite_ex r)

    | UnEx (t, r) -> UnEx (t, rewrite_ex r)

    | _ as e -> e
    in
    let on_sect l = function
    | SAssign assigns as asgn ->
        asgn :: l (* keep as is *)

    | STrans es ->
        (STrans (List.map (fun e -> compute_consts (rewrite_ex e)) es)) :: l

    | SInit es ->
        (SInit (List.map (fun e -> compute_consts (rewrite_ex e)) es)) :: l

    | SInvar es ->
        (SInvar (List.map (fun e -> compute_consts (rewrite_ex e)) es)) :: l

    | SVar decls ->
        let on_decl l (v, t) =
            if is_vis v#mangled_name
            then (v, t) :: l
            else l
        in
        let left = List.fold_left on_decl [] (List.rev decls) in
        if left <> [] then (SVar left) :: l else l

    | SModInst (inst_name, mod_type, params) as mod_inst ->
        if (Str.string_before inst_name 2) = "p_"
                && (not (is_vis (Str.string_after inst_name 2)))
        then l (* hide *)
        else mod_inst :: l
    in
    let on_top l = function
    | SModule (mod_type, args, sections) ->
        (SModule (mod_type, args,
            (List.fold_left on_sect [] (List.rev sections)))) :: l

    | SLtlSpec (name, e) ->
        (SLtlSpec (name, compute_consts (rewrite_ex e))) :: l

    | SInvarSpec (name, e) ->
        (SInvarSpec (name, compute_consts (rewrite_ex e))) :: l

    | SJustice e ->
        (SJustice (compute_consts (rewrite_ex e))) :: l
    in
    List.fold_left on_top [] (List.rev sections)


let transform rt out_name intabs_prog ctrabs_prog =
    let out = open_out (out_name ^ ".smv") in
    let main_sects, proc_mod_defs = create_proc_mods rt intabs_prog in
    let init_main = init_of_ctrabs rt intabs_prog ctrabs_prog in
    let ctr_main, ctr_mods = create_counter_mods rt ctrabs_prog in
    let forms = create_counter_specs rt ctrabs_prog in
    let all_main_sects = main_sects @ ctr_main @ init_main in
    let tops = SModule ("main", [], all_main_sects)
            :: forms @ proc_mod_defs @ ctr_mods in
    let globals =
        List.map (fun v -> v#mangled_name) (collect_globals all_main_sects) in
    let hidden = NusmvPass.create_or_read_names globals "main-ssa-hidden.txt" in
    let hidden_set =
        List.fold_left (fun s n -> StrSet.add n s) StrSet.empty hidden in
    let visible_sections = hide_vars hidden_set tops in
    List.iter (fun t -> fprintf out "%s\n" (top_s t)) visible_sections;
    close_out out

