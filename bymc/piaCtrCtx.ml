open Printf

open AbsBasics
open Accums
open Spin
open SpinIr
open VarRole

(*
Counter abstraction context. Each process prototype has its own counter
abstraction context as the abstraction depends on the local state space.
 *)
class ctr_abs_ctx dom role_tbl proctype_name abbrev_name =
    (* TODO: rename to pia_ctr_ctx *)
    object(self)
        val mutable control_vars: var list = []
        val mutable control_size = 0
        val mutable data_vars = []
        val mutable var_sizes: (var, int) Hashtbl.t = Hashtbl.create 1
        val ctr_var = new var ("bymc_k" ^ abbrev_name)
        val spur_var = new var "bymc_spur"
        
        initializer
            let is_proc_var v = (v#proc_name = proctype_name) in
            let cvs = List.filter is_proc_var
                (hashtbl_filter_keys is_bounded role_tbl#get_all) in
            if cvs == []
            then begin
                let m = "No status variable (like pc) in "
                    ^ proctype_name ^ " found." in
                raise (Abstraction_error m)
            end;
            control_vars <- cvs;
            let var_dom_size v =
                match role_tbl#get_role v with
                | BoundedInt (a, b) ->
                    if is_proc_var v then (b - a) + 1 else 1
                | _ -> 1
            in
            control_size <- List.fold_left ( * ) 1 (List.map var_dom_size control_vars);
            List.iter (fun v -> Hashtbl.add var_sizes v (var_dom_size v)) control_vars;
            let dvs = List.filter is_proc_var
                (hashtbl_filter_keys is_local_unbounded role_tbl#get_all) in
            data_vars <- dvs;
            List.iter (fun v -> Hashtbl.add var_sizes v dom#length) data_vars;
            ctr_var#set_isarray true;
            ctr_var#set_num_elems
                ((ipow dom#length (List.length data_vars))  * control_size);
            spur_var#set_type SpinTypes.TBIT
           
        method proctype_name = proctype_name
        method abbrev_name = abbrev_name

        method get_control_vars = control_vars
        method get_control_size = control_size
        method get_locals = data_vars
        method get_ctr = ctr_var
        method get_ctr_dim = ctr_var#get_num_elems
        method get_spur = spur_var

        method var_vec = (self#get_locals @ self#get_control_vars)

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
    end
;;


(* Collection of counter abstraction contexts: one for a process prototype. *)
class ctr_abs_ctx_tbl dom role_tbl prog =
    object(self)
        val mutable tbl: (string, ctr_abs_ctx) Hashtbl.t
            = Hashtbl.create (List.length (Program.get_procs prog))
        val mutable abbrev_tbl: (string, ctr_abs_ctx) Hashtbl.t
            = Hashtbl.create (List.length (Program.get_procs prog))
        val spur_var = new var "bymc_spur"
        
        initializer
            let mk p =
                let pname = p#get_name in
                let abbrev = str_shorten tbl pname in
                let c_ctx = new ctr_abs_ctx dom role_tbl pname abbrev in
                Hashtbl.add tbl pname c_ctx;
                Hashtbl.add abbrev_tbl abbrev c_ctx
            in
            List.iter mk (Program.get_procs prog)

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
    end
;;

