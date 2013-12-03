(*
 Translating processes in SSA and encoding them in NuSMV format.
 This is the third try to create an efficient encoding in NuSMV.
 *)

open Printf

open AbsSimple
open Accums
open Cfg
open CfgSmt
open Debug
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

let is_var_local_in = function
    | LocalIn _ -> true
    | _ -> false

let is_var_local_out = function
    | LocalOut _ -> true
    | _ -> false

let is_var_shared_in = function
    | SharedIn _ -> true
    | _ -> false

let is_var_shared_out = function
    | SharedOut _ -> true
    | _ -> false

let is_var_shared = function
    | SharedIn (v, _) -> true
    | SharedOut (v, _) -> true
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
let attach_out v = v#fresh_copy (v#get_name ^ "_OUT")


let partition_var tt shared v =
    let vlen = String.length v#get_name in
    let is_in = vlen > 3 && (Str.last_chars v#get_name 3) = "_IN" in
    let is_out = vlen > 4 && (Str.last_chars v#get_name 4) = "_OUT" in
    let t = tt#get_type v in
    match (is_in, is_out) with
    | (true, _) ->
            let name =
                String.sub v#get_name 0 ((String.length v#get_name) - 3)
            in
            if StringSet.mem name shared
            then SharedIn (v, t)
            else LocalIn (v, t)
    | (_, true) ->
            let name =
                String.sub v#get_name 0 ((String.length v#get_name) - 4)
            in
            if StringSet.mem name shared
            then SharedOut (v, t)
            else LocalOut (v, t)
    | _ -> Temp (v, t)


let replace_with_next syms tt shared v =
    match partition_var tt shared v with
    | SharedOut (_, _) ->
        let inm = (strip_out v#get_name) ^ "_IN" in
        let inv =
            try (syms#lookup inm)#as_var
            with Symbol_not_found _ ->
                (* it might happen that we have x_OUT only *)
                let nv = v#fresh_copy inm in
                syms#add_symb inm (nv :> symb);
                nv
        in
        UnEx (NEXT, Var inv)

    | _ -> Var v 

let vars_of_syms syms =
    let is_var s = s#get_sym_type = SymVar in
    List.map (fun s -> s#as_var) (List.filter is_var syms)


(* As symbolic tables use variable names for lookup,
  the local variables of different processes may collide.
  Rename the variables to their mangled versions.
 *)
let rename_vars tt shared seq =
    let tab = Hashtbl.create 8 in
    let sub v =
        if StringSet.mem v#mangled_name shared
        then Var v
        else
            try Var (Hashtbl.find tab v#id)
            with Not_found ->
                let nv = v#copy v#mangled_name in
                nv#set_proc_name ""; (* make them global *)
                Hashtbl.replace tab v#id nv;
                Var nv
    in
    let each_stmt s =
        let mape e = map_vars sub e in
        map_expr_in_lir_stmt mape s
    in
    (hashtbl_vals tab, List.map each_stmt seq)


(* ====================== important functions *)

let module_of_proc rt out_becomes_next prog =
    let procs = Program.get_procs prog in
    let nprocs = List.length procs in
    let shared = Program.get_shared prog in
    let shared_set =
        List.fold_left (fun s v -> StringSet.add v#get_name s)
            StringSet.empty shared in
    let mono_proc_name =
        str_join "_" (List.map (fun p -> p#get_name) procs) in

    (* process id is chosen non-deterministically for each step *)
    let pid = new_var "_pid" in
    pid#set_proc_name mono_proc_name;
    let pidt = new data_type SpinTypes.TINT in
    pidt#set_range 0 nprocs;

    let new_type_tab = (Program.get_type_tab prog)#copy in
    new_type_tab#set_type pid pidt;
    let new_sym_tab = new symb_tab mono_proc_name in
    new_sym_tab#add_symb pid#mangled_name (pid :> symb);

    (* we need only the computation region (from every process) *)
    let get_comp p =
        let reg_tab = (rt#caches#find_struc prog)#get_regions p#get_name
        in
        reg_tab#get "comp" p#get_stmts 
    in

    (* both locals and shared are the parameters of our module *)
    let make_options p i =
        let choose =
            MExpr (fresh_id (), (BinEx (ASGN, Var pid, Const i))) in
        MOptGuarded (choose :: (get_comp p))
    in
    (* we have a single process for everything *)
    let mono_proc_code =
        let opts = List.map2 make_options procs (range 0 nprocs) in
        [MIf (fresh_id (), opts)]
    in
    let new_locals, all_stmts =
        rename_vars new_type_tab shared_set (mir_to_lir mono_proc_code)
    in
    let to_ssa =
        (* construct SSA as in SmtXducerPass *)
        let cfg = Cfg.remove_ineffective_blocks (mk_cfg all_stmts) in
        let cfg_ssa =
            mk_ssa rt#solver false (pid :: shared @ new_locals) []
                new_sym_tab new_type_tab cfg in
        Cfg.write_dot (sprintf "ssa-comp-%s.dot" mono_proc_name) cfg_ssa;
        let exprs = cfg_to_constraints
                mono_proc_name new_sym_tab new_type_tab cfg_ssa
        in
        (new_type_tab, new_sym_tab, List.map expr_of_m_stmt exprs)
    in
    let ntt, syms, exprs = to_ssa in
    let new_vars = vars_of_syms syms#get_symbs in
    (* we have to constrain the variables with the invariant to cut out
       the deadlock behaviour when the input variables do not match
       the process code *)
    let is_nuked v =
        is_var_shared_out (partition_var ntt shared_set v) in
    let invar =
        if out_becomes_next
        then List.map (nuke_vars is_nuked) exprs
        else exprs
    in
    (* for the transition relation we either replace x_OUT with
       next(x), or keep it as it is (for the reachability) *)
    let exprs =
        if out_becomes_next
        then List.map
            (map_vars (replace_with_next syms ntt shared_set)) exprs
        else exprs
    in
    let pvars =
        List.sort proc_var_cmp
            (List.map (partition_var ntt shared_set) new_vars)
    in
    (* input versions of the local variables as well as temporary
       copies must stay local *)
    let temps =
        List.filter (fun v -> is_var_temp v || is_var_local_in v) pvars
    in
    let args =
        if out_becomes_next
        then (* x_OUT becomes next(x) *)
            let f v = is_var_local_out v || is_var_shared_in v in
            List.filter f pvars
        else (* x_OUT stays as x_OUT *)
            let f v = is_var_local_out v || is_var_shared v in
            List.filter f pvars
    in
    let invar_at0 = Var ((syms#lookup "at0")#as_var) in
    let mod_type =
        SModule (mono_proc_name,
            List.map ptov args,
            [SVar (List.map ptovt temps);
             SInvar (invar_at0 :: invar);
             STrans exprs])
    in
    (mono_proc_name, mod_type, args, new_sym_tab, new_type_tab)


let create_proc_mods rt out_becomes_next intabs_prog =
    let proc_name, mod_type, args, nst, ntt =
        module_of_proc rt out_becomes_next intabs_prog in
    let to_shared_param l = function
        | SharedIn (v, t) ->
            (v#copy (strip_in v#get_name), t) :: l
        | SharedOut (v, t) ->
            if out_becomes_next
            then (v#copy (strip_out v#get_name), t) :: l
            else (v, t) :: l

        | _ -> l
    in
    let to_local_param l = function
        | LocalIn (v, t) ->
            log WARN (sprintf 
                "Local variable %s is not always assigned."
                (strip_in v#mangled_name));
            l
        | LocalOut (v, t) ->
            (v#copy (strip_out v#get_name), t) :: l
        | _ -> l
    in
    let shared_params = 
        List.fold_left to_shared_param [] (List.rev args) in
    let local_params = 
        List.fold_left to_local_param [] (List.rev args) in

    trace Trc.nse (fun _ ->
        "local_params: " ^
            (str_join ", " (List.map var_qname (List.map fst local_params))));

    let inst = SModInst("p_" ^ proc_name, proc_name,
        (List.map (fun (v, _) -> Var v) (shared_params @ local_params)))
    in
    let tt = Program.get_type_tab intabs_prog in
    let shared = Program.get_shared intabs_prog in
    let shared_in = List.map (fun v -> (v, tt#get_type v)) shared in
    let shared_out =
        if out_becomes_next
        then []
        else List.map (fun v -> (attach_out v, tt#get_type v)) shared
    in
    let pid = (nst#lookup (proc_name ^ "___pid"))#as_var in
    ([SVar (shared_in @ shared_out); SVar local_params; inst],
        [mod_type], nst, ntt, pid)


(* partially copied from nusmvCounterClusterPass *)
(* TODO: deal with many process types *)
let module_of_counter rt proc_syms proc_types ctrabs_prog pid p num =
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
    let next_eq = cmp_idx AND EQ next_locals in
    let myval = new_var "myval" in
    let mk_case local_ex prev_val next_vals =
        let guard =
            BinEx (AND, local_ex, BinEx (EQ, Var myval, Const prev_val))
        in
        let rhs = List.map (fun i -> Const i) next_vals in
        (guard, rhs)
    in
    let prev_cases = hashtbl_map (mk_case prev_eq) dec_tbl in
    let next_cases = hashtbl_map (mk_case next_eq) inc_tbl in
    let cases =
        (* if the process is not selected, keep the value *)
          (BinEx (NE, Var pid, Const num), [Var myval])
        (* if the in and out coincide, keep the value *)
        :: (BinEx (AND, prev_eq, next_eq), [Var myval])
        (* decrease if the process moves out of this location *)
        :: prev_cases
        (* increase if the process moves into this location *)
        @ next_cases
        (* keep as before *)
        @ [(Var nusmv_true, [Var myval])]
    in
    let choice = SAssign [ANext (myval, cases)] in
    let args =
        pid :: myval :: (List.map my_var prev_locals)
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
        t#set_range 0 3;
        SVar [(bymc_loc, t)]
    in
    let change_loc =
        ANext (bymc_loc, [(Var nusmv_true, [ Const 2 (* TODO: 0? *) ])]) 
    in
    [ bymc_loc_decl; SInit init_ess; SAssign [change_loc] ]
    


let create_counter_mods rt proc_syms proc_types ctrabs_prog pid =
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
            let get_val v =
                try Const (Hashtbl.find valtab v)
                with Not_found ->
                    raise (Failure ("Not found " ^ v#get_name))
            in
            let tov v = Var v in
            let params =
                (tov pid) :: (tov myctr) :: (List.map get_val prev)
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
        List.fold_left per_idx l
            (ctr_ctx#all_indices_for (fun _ -> true))
    in
    let procs = Program.get_procs ctrabs_prog in
    let nprocs = List.length procs in
    let main_sects = List.fold_left create_vars [] procs in
    let mods =
        List.map2 (module_of_counter rt proc_syms
                   proc_types ctrabs_prog pid)
        procs (range 0 nprocs) in
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
    Accums.StringMap.fold
            (create_spec sym_tab) (Program.get_ltl_forms ctrabs_prog) []


let create_counter_non_spurious rt ctrabs_prog globals =
    let syms = new symb_tab "glob" in
    List.iter (fun v -> syms#add_symb v#get_name (v :> symb)) globals;
    let each_step (pre, post) =
        let pre = Simplif.replace_arr_elem_with_var syms pre in
        let post = Simplif.replace_arr_elem_with_var syms post in
        let next_post = map_vars (fun v -> UnEx (NEXT, Var v)) post in
        (* either precondition or postcondition do not hold *)
        let pre = if not_nop pre then pre else Var nusmv_true in
        let next_post =
            if not_nop next_post then next_post else Var nusmv_true in
        BinEx (OR, UnEx (NEG, pre), UnEx (NEG, next_post))
    in
    let spurious = Program.get_spurious_steps ctrabs_prog in
    if spurious <> []
    then [STrans (List.map each_step spurious)]
    else []


let reach_inv_of_ctrabs rt ctrabs_prog =
    let create_reach lst p =
        let ctr_ctx =
            rt#caches#analysis#get_pia_ctr_ctx_tbl#get_ctx p#get_name in
        let ctr = ctr_ctx#get_ctr in
        let idx_spec l idx = 
            let name = sprintf "r_%s_%dI" ctr#get_name idx in
            let vals = ctr_ctx#unpack_from_const idx in
            let f n v a = (BinEx (NE, Var n, Const v)) :: a in
            (SInvarSpec (name, list_to_binex OR (Hashtbl.fold f vals []))) :: l
        in
        List.fold_left idx_spec lst (ctr_ctx#all_indices_for (fun _ -> true))
    in
    List.fold_left create_reach [] (Program.get_procs ctrabs_prog)


(* initialize the processes' variables to the initial values *)
let exec_of_ctrabs_procs rt intabs_prog ctrabs_prog pid =
    let init_of_proc l p =
        (* find all possible valuations of the local variables *)
        let ctr_ctx =
            rt#caches#analysis#get_pia_ctr_ctx_tbl#get_ctx p#get_name in
        let reg_tab =
            (rt#caches#find_struc intabs_prog)#get_regions p#get_name in
        let init = reg_tab#get "init" p#get_stmts in
        let decl = reg_tab#get "decl" p#get_stmts in
        let init_vals = AbsCounter.find_init_local_vals ctr_ctx decl init in
        let to_and asgns =
            list_to_binex AND
                (List.map (fun (v, i) -> BinEx (EQ, Var v, Const i)) asgns) in
        let ex = list_to_binex OR (List.map to_and init_vals) in
        ex :: l
    in
    let bind_locals l p num =
        let ctr_ctx =
            rt#caches#analysis#get_pia_ctr_ctx_tbl#get_ctx p#get_name in
        let bind lst v =
            let n = ctr_ctx#get_next v in
            let enabled = BinEx (EQ, Var pid, Const num) in
            let disabled = BinEx (NE, Var pid, Const num) in
            let move_or_keep =
                BinEx (AND,
                    BinEx (IMPLIES,
                           enabled, 
                           BinEx (EQ, UnEx (NEXT, Var v), Var n)),
                    BinEx (IMPLIES,
                           disabled,
                           BinEx (EQ, UnEx (NEXT, Var v), Var v))) in
            move_or_keep :: lst
        in
        List.fold_left bind l ctr_ctx#var_vec
    in
    let procs = Program.get_procs intabs_prog in
    let nprocs = List.length procs in
    let init_ess = List.fold_left init_of_proc [] procs in
    let trans_ess =
        List.fold_left2 bind_locals [] procs (range 0 nprocs) in
    [ SInit init_ess; STrans trans_ess ]


let collect_globals main_sect =
    let f lst = function
    | SVar decls -> (List.fold_left (fun  l (v, _) -> v :: l) lst decls)
    | _ -> lst
    in
    List.fold_left f [] main_sect


let hide_vars names sections =
    let is_vis n = not (StrSet.mem n names)
    in
    let simplify e =
        let rec rewrite = function
        | Var v as e ->
            if is_vis v#mangled_name
            then e
            else Const 0  (* unreachable meaning always 0 *)

        | BinEx (EQ, Var v, Const i) as e ->
            if is_vis v#mangled_name
            then e
            (* unreachable meaning always 0 *)
            else if i > 0 then Const 0 else Const 1

        | BinEx (NE, Var v, Const i) as e ->
            if is_vis v#mangled_name
            then e
            (* unreachable, always 0 *)
            else if i > 0 then Const 1 else Const 0

        | BinEx (t, l, r) -> BinEx (t, rewrite l, rewrite r)

        | UnEx (t, r) -> UnEx (t, rewrite r)

        | _ as e -> e
        in
        compute_consts (rewrite e)
    in
    let on_sect l = function
    | SAssign assigns as asgn ->
        asgn :: l (* keep as is *)

    | STrans es ->
        (STrans (List.map (fun e -> compute_consts (simplify e)) es)) :: l

    | SInit es ->
        (SInit (List.map (fun e -> compute_consts (simplify e)) es)) :: l

    | SInvar es ->
        (SInvar (List.map (fun e -> compute_consts (simplify e)) es)) :: l

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
        (SLtlSpec (name, compute_consts (simplify e))) :: l

    | SInvarSpec (name, e) ->
        (SInvarSpec (name, compute_consts (simplify e))) :: l

    | SJustice e ->
        (SJustice (compute_consts (simplify e))) :: l
    in
    List.fold_left on_top [] (List.rev sections)


let transform rt out_name intabs_prog ctrabs_prog =
    let out = open_out (out_name ^ ".smv") in
    let main_sects, proc_mod_defs, proc_st, proc_tt, pid =
        create_proc_mods rt true intabs_prog in
    let init_main = init_of_ctrabs rt intabs_prog ctrabs_prog in
    let ctr_main, ctr_mods =
        create_counter_mods rt proc_st proc_tt ctrabs_prog pid in
    let forms = create_counter_specs rt ctrabs_prog in
    let globals = collect_globals (main_sects @ ctr_main) in
    let non_spurious = create_counter_non_spurious rt ctrabs_prog globals in
    let all_main_sects = main_sects @ ctr_main @ init_main @ non_spurious in
    let tops = SModule ("main", [], all_main_sects)
            :: forms @ proc_mod_defs @ ctr_mods in
    let globals =
        List.map (fun v -> v#mangled_name) (collect_globals all_main_sects) in
    let hidden = NusmvPass.create_or_read_names
        rt#caches#options globals "main-ssa-hidden.txt"
    in
    log INFO (sprintf "    %d variables are hidden\n" (List.length hidden));
    let hidden_set =
        List.fold_left (fun s n -> StrSet.add n s) StrSet.empty hidden in
    let visible_sections = hide_vars hidden_set tops in
    List.iter (fun t -> fprintf out "%s\n" (top_s t)) visible_sections;
    close_out out


let mk_counter_reach rt out_name intabs_prog ctrabs_prog =
    let out = open_out (out_name ^ ".smv") in
    let main_sects, proc_mod_defs, _, _, pid =
        create_proc_mods rt false intabs_prog in
    let exec_procs =
        exec_of_ctrabs_procs rt intabs_prog ctrabs_prog pid in
    let invs = reach_inv_of_ctrabs rt ctrabs_prog in
    let all_main_sects = main_sects @ exec_procs in
    let tops = SModule ("main", [], all_main_sects) :: invs @ proc_mod_defs in
    List.iter (fun t -> fprintf out "%s\n" (top_s t)) tops;
    close_out out

