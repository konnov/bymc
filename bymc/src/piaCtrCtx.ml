open Printf

open AbsBasics
open Accums
open Analysis
open SkelStruc
open Spin
open SpinIr
open SpinIrImp
open VarRole

(*
Counter abstraction context. Each process prototype has its own counter
abstraction context as the abstraction depends on the local state space.
 *)
class ctr_abs_ctx dom role_tbl (spur_var: var) proc abbrev_name =
    (* TODO: rename to pia_ctr_ctx *)
    object(self)
        val mutable control_vars: var list = []
        val mutable control_size = 0
        val mutable data_vars = []
        val mutable m_var_vec: (var * int) list = []
        val ctr_var = new_var ("bymc_k" ^ abbrev_name)
        val mutable ctr_dim: int = -1
        (* Pairs of the variable before the loop body and after the loop body.
           This list is usually tiny.
           TODO: move out this relation, as it can be used with any
           finite-state process body. There is not so much special about
           counter abstraction here.
         *)
        val mutable m_next_vars: (var * var) list = []

        method init_next_vars =
            let reg_tab = extract_skel proc#get_stmts in
            let update = reg_tab#get "update" proc#get_stmts in
            m_next_vars <- hashtbl_as_list (find_copy_pairs (mir_to_lir update))
        
        initializer
            self#init_next_vars;

            let collect_locals filter_fun =
                let rec collect lst = function
                | MDecl (_, v, _) ->
                    if filter_fun (role_tbl#get_role v)
                    then v :: lst
                    else lst
                | _ -> lst
                in
                List.fold_left collect [] proc#get_stmts
            in
            let cvs = collect_locals is_bounded in
            if cvs == []
            then begin
                let m = "No status variable (like pc) in "
                    ^ proc#get_name ^ " found." in
                raise (Abstraction_error m)
            end;
            control_vars <- cvs;
            let var_dom_size v =
                match role_tbl#get_role v with
                | BoundedInt (a, b) -> (b - a) + 1
                | _ -> 1
            in
            control_size <- List.fold_left ( * ) 1 (List.map var_dom_size control_vars);
            let dvs = collect_locals is_local_unbounded in
            data_vars <- dvs;
            ctr_dim <-
                ((ipow dom#length (List.length data_vars))  * control_size);
            m_var_vec <-
                List.map (fun v -> (v, dom#length)) data_vars
              @ List.map (fun v -> (v, var_dom_size v)) control_vars
           
        method proctype_name = proc#get_name
        method abbrev_name = abbrev_name

        method get_control_vars = control_vars
        method get_control_size = control_size
        method get_locals = data_vars
        method get_ctr = ctr_var
        method get_ctr_dim = ctr_dim
        method get_spur = spur_var

        method var_vec = List.map fst m_var_vec

        method get_next (prev: var): var =
            try snd (List.find (fun (p, n) -> p#id = prev#id) m_next_vars)
            with Not_found -> raise (Failure ("no next var for " ^ prev#qual_name))

        method prev_next_pairs = m_next_vars

        method unpack_from_const i =
            let valuation = Hashtbl.create (List.length m_var_vec) in
            let unpack_one big_num (v, sz) =
                Hashtbl.add valuation v (big_num mod sz);
                (big_num / sz) in
            let _ = List.fold_left unpack_one i m_var_vec in
            valuation

        method pack_to_const valuation =
            let get_val v =
                try Hashtbl.find valuation v
                with Not_found ->
                    raise (Failure
                        (sprintf "Valuation of %s not found" v#qual_name))
            in
            let pack_one sum (v, sz) = sum * sz + (get_val v) in
            List.fold_left pack_one 0 (List.rev m_var_vec)

        method pack_index_expr =
            let pack_one subex (v, sz) =
                if is_nop subex
                then Var v
                else let shifted = BinEx (MULT, subex, Const sz) in
                    BinEx (PLUS, shifted, Var v)
            in
            List.fold_left pack_one (Nop "") (List.rev m_var_vec)

        method all_indices_for check_val_fun =
            let has_v i = (check_val_fun (self#unpack_from_const i)) in
            List.filter has_v (range 0 self#get_ctr_dim)


        method dump (out: out_channel) =
            let print_kv k v =
                Printf.fprintf out "%s = %d; " k#qual_name v in
            let print_index i =
                let vals = self#unpack_from_const i in
                Printf.fprintf out "%s[%d] -> " ctr_var#qual_name i;
                Hashtbl.iter print_kv vals;
                Printf.fprintf out "\n"
            in
            List.iter print_index (range 0 self#get_ctr_dim)

    end


(* Collection of counter abstraction contexts: one for a process prototype. *)
class ctr_abs_ctx_tbl dom role_tbl prog procs =
    object(self)
        val mutable tbl: (string, ctr_abs_ctx) Hashtbl.t
            = Hashtbl.create (List.length procs)
        val mutable abbrev_tbl: (string, ctr_abs_ctx) Hashtbl.t
            = Hashtbl.create (List.length procs)
        val spur_var = new_var "bymc_spur"
        
        initializer
            spur_var#set_instrumental;
            let mk p =
                let pname = p#get_name in
                let abbrev = str_shorten tbl pname in
                let c_ctx = new ctr_abs_ctx dom role_tbl spur_var p abbrev in
                Hashtbl.add tbl pname c_ctx;
                Hashtbl.add abbrev_tbl abbrev c_ctx
            in
            List.iter mk procs;
            let o = open_out "pia_ctr.txt" in
            self#dump o;
            close_out o

        method get_ctx name =
            try Hashtbl.find tbl name
            with Not_found -> raise (Failure ("No context for " ^ name))

        method get_ctx_by_abbrev short =
            try Hashtbl.find abbrev_tbl short
            with Not_found -> raise (Failure ("No context for " ^ short))

        method all_counters =
            List.map (fun c -> c#get_ctr) (hashtbl_vals tbl)

        method all_ctxs = hashtbl_vals tbl

        method get_spur = spur_var

        method dump out =
            List.iter (fun c -> c#dump out) self#all_ctxs
    end

