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
        val mutable var_sizes: (var, int) Hashtbl.t = Hashtbl.create 1
        val ctr_var = new_var ("bymc_k" ^ abbrev_name)
        val mutable ctr_dim: int = -1
        val mutable m_next_vars: (var, var) Hashtbl.t = Hashtbl.create 1

        method init_next_vars =
            let reg_tab = extract_skel proc#get_stmts in
            let update = reg_tab#get "update" proc#get_stmts in
            m_next_vars <- find_copy_pairs (mir_to_lir update)
        
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
            List.iter (fun v -> Hashtbl.add var_sizes v (var_dom_size v)) control_vars;
            let dvs = collect_locals is_local_unbounded in
            data_vars <- dvs;
            List.iter (fun v -> Hashtbl.add var_sizes v dom#length) data_vars;
            ctr_dim <-
                ((ipow dom#length (List.length data_vars))  * control_size)
           
        method proctype_name = proc#get_name
        method abbrev_name = abbrev_name

        method get_control_vars = control_vars
        method get_control_size = control_size
        method get_locals = data_vars
        method get_ctr = ctr_var
        method get_ctr_dim = ctr_dim
        method get_spur = spur_var

        method var_vec = (self#get_locals @ self#get_control_vars)

        method get_next v =
            try Hashtbl.find m_next_vars v
            with Not_found -> raise (Failure ("no next var for " ^v#get_name))

        method prev_next_pairs =
            hashtbl_as_list m_next_vars

        method unpack_from_const i =
            let vsz v = Hashtbl.find var_sizes v in
            let valuation = Hashtbl.create (List.length self#var_vec) in
            let unpack_one big_num var =
                Hashtbl.add valuation var (big_num mod (vsz var));
                big_num / (vsz var) in
            let _ = List.fold_left unpack_one i self#var_vec in
            valuation

        method pack_to_const valuation =
            let get_val var =
                try Hashtbl.find valuation var
                with Not_found ->
                    raise (Failure
                        (sprintf "Valuation of %s not found" var#get_name))
            in
            let pack_one sum var =
                sum * (Hashtbl.find var_sizes var) + (get_val var) in
            List.fold_left pack_one 0 (List.rev self#var_vec)

        method pack_index_expr =
            let pack_one subex var =
                if is_nop subex
                then Var var
                else let shifted =
                        BinEx (MULT, subex, Const (Hashtbl.find var_sizes var)) in
                    BinEx (PLUS, shifted, Var var)
            in
            List.fold_left pack_one (Nop "") (List.rev self#var_vec)

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

