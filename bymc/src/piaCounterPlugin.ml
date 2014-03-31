open AbsInterval
open AbsCounter
open Debug
open Invariant
open PiaCtrCtx
open PiaDataCtx
open PiaDataPlugin
open Plugin
open Program
open PiaCtrRefinement
open SkelStruc
open Spin
open SpinIr
open SpinIrImp
open Writer

class pc_plugin_t (plugin_name: string) =
    object(self)
        inherit transform_plugin_t plugin_name

        val mutable m_ctr_abs_ctx_tbl: ctr_abs_ctx_tbl option = None
        val mutable m_ref_step = 0 (* refinement step *)
        val mutable m_vass = Program.empty

        (* TODO: to be removed *)
        method semi_prog = self#get_input1

        method transform rt =
            let prog = self#get_input0 in
            let semiprog = self#get_input1 in
            let caches = rt#caches in
            let solver = rt#solver in
            let dom = caches#analysis#get_pia_dom in
            let proc_names = 
                if self#has_opt rt "procs"
                then Str.split (Str.regexp_string ",") (self#get_opt rt "procs")
                else List.map (fun p -> p#get_name) (Program.get_procs prog)
            in
            let is_included p = List.mem p#get_name proc_names in
            let procs = List.filter is_included (Program.get_procs prog) in
            let proc_struc = caches#find_struc prog in
            let ctx = new ctr_abs_ctx_tbl prog proc_struc procs in
            m_ctr_abs_ctx_tbl <- Some ctx;
            caches#analysis#set_pia_ctr_ctx_tbl ctx;

            (* construct VASS *)
            if m_ref_step = 0
            then begin
                (* TODO: the following MUST be set in piaDataPlugin only! *)
                caches#analysis#get_pia_data_ctx#set_hack_shared true;
                let vass =
                    self#make_vass solver dom caches semiprog proc_names false
                in
                log INFO "  check the invariants";
                check_all_invariants rt vass;
                (* TODO: the following MUST be set in piaDataPlugin only! *)
                caches#analysis#get_pia_data_ctx#set_hack_shared false;
                log INFO "  save the symbolic transition relation";
                m_vass <-
                    self#make_vass solver dom caches semiprog proc_names true
            end;

            (* construct counter abstraction *)
            let funcs = new abs_ctr_funcs dom prog solver in
            log INFO "> Constructing counter abstraction";
            let ctrabs_prog =
                do_counter_abstraction funcs solver caches prog proc_names
            in
            write_to_file false "abs-counter-general.prm"
                (units_of_program ctrabs_prog) (get_type_tab ctrabs_prog)
                (Hashtbl.create 10);
            log INFO "[DONE]";
            ctrabs_prog

        method private make_vass solver dom caches prog proc_names embed_inv =
            log INFO "> Constructing VASS...";
            let vass_funcs = new vass_funcs dom prog solver in
            vass_funcs#set_embed_inv embed_inv;
            let vass_prog =
                do_counter_abstraction vass_funcs solver caches prog proc_names
            in
            caches#set_struc vass_prog (compute_struc vass_prog);
            write_to_file false "abs-vass.prm"
                (units_of_program vass_prog) (get_type_tab vass_prog)
                (Hashtbl.create 10);
            log INFO "> Constructing SMT transducers...";
            let xducer_prog =
                SmtXducerPass.to_xducer_interleave solver caches vass_prog in
            write_to_file false "abs-xducers.prm"
                (units_of_program xducer_prog) (get_type_tab xducer_prog)
                (Hashtbl.create 10);
            log INFO "  [DONE]"; flush stdout;
            xducer_prog

        method update_runtime rt =
            rt#caches#set_struc
                (self#get_output) (compute_struc self#get_output);
            (* set counter contexts *)
            match m_ctr_abs_ctx_tbl with
            | Some c -> rt#caches#analysis#set_pia_ctr_ctx_tbl c
            | _ -> ()

        (* for a counter or shared variable x,
           replace x = d_j with g_j <= x < g_{j+1} *)
        method decode_trail rt (prefix, loop) =
            let dom = rt#caches#analysis#get_pia_dom in
            let data_ctx = rt#caches#analysis#get_pia_data_ctx in

            let concretize_ex = function
            | BinEx(EQ, BinEx(ARR_ACCESS, Var a, Const i), Const v) ->
                (* TODO: check, whether "a" is a counter array? *)
                let el = BinEx(ARR_ACCESS, Var a, Const i) in
                let conc_ex = dom#expr_is_concretization el v in
                conc_ex

            | BinEx(EQ, Var x, Const v) as e ->
                if data_ctx#must_keep_concrete (Var x)
                then dom#expr_is_concretization (Var x) v
                else e

            | _ as e ->
                raise (PiaCtrRefinement.Refinement_error
                    ("Don't know how to decode: " ^ (expr_s e)))
            in
            let conc_row = function
                | State path_elem ->
                    State (List.map concretize_ex path_elem)

                | _ as o -> o
            in
            data_ctx#set_hack_shared true; (* concretize shared *)
            let prefix_asrt = List.map conc_row prefix in
            let loop_asrt = List.map conc_row loop in
            data_ctx#set_hack_shared false; (* reset *)
            (prefix_asrt, loop_asrt)


        method refine rt lasso =
            let res, new_prog =
                do_refinement rt m_ref_step self#get_output m_vass lasso in
            if res
            then begin
                m_ref_step <- m_ref_step + 1;
                (true, new_prog)
            end else (false, self#get_output)
    end

