open Printf

open Accums
open Debug
open PiaDataPlugin
open Plugin
open Program
open Serialize
open Spin
open SpinIr
open SpinIrImp

let parse_assignment syms line =
    let ass_re = Str.regexp " *\\([a-zA-Z_][a-zA-Z0-9_]*\\) = \\([0-9]+\\)" in
    let name_re = Str.regexp "\\([a-zA-Z_][a-zA-Z0-9_]*\\)_\\([0-9]+\\)I" in
    if not (Str.string_match ass_re line 0)
    then Nop ""
    else
        try
            let lhs = Str.matched_group 1 line in
            let rhs = int_of_string (Str.matched_group 2 line) in
            let left_ex =
                if not (Str.string_match name_re lhs 0)
                then Var ((syms#lookup lhs)#as_var)
                else let arr = Str.matched_group 1 lhs in
                    let idx = int_of_string (Str.matched_group 2 lhs) in
                    BinEx (ARR_ACCESS, Var ((syms#lookup arr)#as_var), Const idx)
            in
            BinEx (EQ, left_ex, Const rhs)
        with SpinIr.Symbol_not_found _ ->
            Nop "" (* ignore local process variables *)


let add_hidden prog state_es =            
    let tab = Hashtbl.create 8 in
    let assign = function
    | BinEx (EQ, lhs, Const i) as e ->
        Hashtbl.replace tab (expr_s lhs) e
    | _ as e ->
        raise (Failure ("Unexpected expression " ^ (expr_s e)))
    in
    List.iter assign state_es;
    let add_if_needed l e =
        let e_s = expr_s e in
        try (Hashtbl.find tab e_s) :: l
        with Not_found -> (BinEx (EQ, e, Const 0)) :: l
    in
    let _, es = global_state_fmt prog in
    List.rev (List.fold_left add_if_needed [] es)


let print_state prog path_elem =
    let tab = Hashtbl.create 8 in
    let assign = function
    | BinEx (EQ, e, Const i) ->
        Hashtbl.replace tab (expr_s e) i
    | _ as e ->
        raise (Failure ("Unexpected expression " ^ (expr_s e)))
    in
    let state_es =
        match path_elem with
        | State es -> es
        | _ -> []
    in
    List.iter assign state_es;
    let val_fun e =
        let e_s = expr_s e in
        try Hashtbl.find tab e_s
        with Not_found -> raise (Failure ("No value for " ^ e_s))
    in
    let state_s = global_state_s prog val_fun in
    printf "%s\n" state_s


class nusmv_ctr_cluster_plugin_t (plugin_name: string)
        (out_name: string) (pia_data_plugin: pia_data_plugin_t) =

    object(self)
        inherit transform_plugin_t plugin_name

        method is_disabled rt =
            rt#caches#options.Options.mc_tool <> Options.ToolNusmv

        method transform rt prog =
            log INFO (sprintf
                "> writing ssa NuSMV model to %s.smv..." "main-ssa");
            let intabs_prog = pia_data_plugin#get_output in
            NusmvSsaEncoding.transform 
                rt "main-ssa" intabs_prog self#get_input;
            NusmvSsaEncoding.mk_counter_reach
                rt "main-ssa-reach" intabs_prog self#get_input;
            log INFO (sprintf
                "> writing clusterized NuSMV model to %s.smv... SKIPPED" out_name);
            (*
            let caches = rt#caches in
            let solver = rt#solver in
            let roles =
                rt#caches#analysis#get_var_roles pia_data_plugin#get_input in
            NusmvCounterClusterPass.transform
                solver caches roles out_name intabs_prog prog;
                *)
            log INFO "[DONE]";
            prog

        method update_runtime _ =
            ()

        (* we don't know yet how to refine the data abstraction *)
        method decode_trail rt _ =
            let prog = self#get_input in
            let syms = Program.get_sym_tab prog in
            let loop_re = Str.regexp ".*-- Loop starts here.*" in
            let state_re = Str.regexp ".*-> State: [0-9]+\\.[0-9]+ <-" in
            let fin = open_in rt#caches#options.Options.trail_name in
            let loop_pos = ref max_int in
            let trail = ref [] in
            let state_exprs = ref [] in
            let flush_to_trail () =
                if !state_exprs <> []
                then trail := (State (add_hidden prog !state_exprs)) :: !trail;
                state_exprs := []
            in
            begin try
                while true do
                    let line = input_line fin in
                    let state_ex = parse_assignment syms line in
                    if not_nop state_ex
                    then state_exprs := state_ex :: !state_exprs 
                    else if Str.string_match state_re line 0
                    then flush_to_trail ()
                    else if Str.string_match loop_re line 0
                    then loop_pos := 1 + (List.length !trail)
                done
            with End_of_file ->
                flush_to_trail ();
                close_in fin;
            end;

            if !loop_pos = max_int
            then loop_pos := List.length !trail;
            let path = List.rev !trail in
            let prefix = list_sub path 0 !loop_pos in
            List.iter (print_state prog) prefix;
            let lasso = list_sub path !loop_pos ((List.length path) - !loop_pos)
            in
            printf "<<<<<START OF CYCLE>>>>>\n";
            List.iter (print_state prog) lasso;

            if may_log DEBUG
            then begin
                let ps = function
                    | State es ->
                        List.iter (fun e -> printf "%s; " (expr_s e)) es;
                        printf "\n"
                    | Intrinsic map ->
                        printf "Intrinsic: %s\n" (str_map_s (fun s -> s) map)
                in
                printf "SpinPlugin: PREFIX:\n";
                List.iter ps prefix;
                printf "SpinPlugin: LASSO:\n";
                List.iter ps lasso
            end;
            (prefix, lasso)

        method refine _ path = (false, self#get_output)
    end

