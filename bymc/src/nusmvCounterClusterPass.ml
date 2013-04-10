(*
  An optimized encoding of counter representation that represent each
  counter as a module. This allows nusmv to use clusters, which are much
  more efficient for large models.

  Igor Konnov, 2013
 *)

open Printf

open AbsBasics
open Accums
open Spin
open SpinIr
open SpinIrImp

let collect_rhs solver dom op =
    solver#push_ctx;
    let x = new var "x" (fresh_id ()) in
    let y = new var "y" (fresh_id ()) in
    let tp = new data_type SpinTypes.TINT in
    tp#set_range 0 dom#length; (* counters are bounded *)
    solver#append_var_def x tp; 
    solver#append_var_def y tp; 
    let tbl = Hashtbl.create 10 in
    let chg = BinEx (EQ, Var x, BinEx (op, Var y, Const 1)) in
    let on_point p =
        let add xv yv =
            if Hashtbl.mem tbl xv
            then Hashtbl.replace tbl xv (yv :: (Hashtbl.find tbl xv))
            else Hashtbl.add tbl xv [yv]
        in
        match p with
        | ((x1, v1) :: (_, v2) :: []) ->
            if x1#id = x#id then add v1 v2 else add v2 v1
        | _ -> raise (Failure "oops?")
    in
    let points_lst = dom#find_abs_vals ExistAbs solver chg in
    solver#pop_ctx;
    List.iter on_point points_lst;
    tbl


let create_proc_counters solver caches out proc =
    let ctr_ctx =
        caches#analysis#get_pia_ctr_ctx_tbl#get_ctx proc#get_name in
    let dom = caches#analysis#get_pia_dom in
    let dec_tbl = collect_rhs solver dom PLUS in
    let inc_tbl = collect_rhs solver dom MINUS in
    let create_module idx =
        let valtab = ctr_ctx#unpack_from_const idx in
        (* XXX: fix params, they should include next *)
        let params = str_join ", "
            (List.map (fun v -> v#mangled_name) (hashtbl_keys valtab)) in
        let next_name v =
            let next = ctr_ctx#get_next v in
            next#mangled_name in
        let next_params = str_join ", "
            (List.map next_name (hashtbl_keys valtab)) in
        let mk_prev con op =
            let f (k, v) = sprintf "%s %s %d" k#mangled_name op v in
            str_join con (List.map f (hashtbl_as_list valtab)) in
        let prev_eq = mk_prev " & " "=" in
        let prev_neq = mk_prev " | " "!=" in
        let mk_next con op =
            let f (k, v) =
                sprintf "%s %s %d" (ctr_ctx#get_next k)#mangled_name op v in
            str_join con (List.map f (hashtbl_as_list valtab)) in
        let next_eq = mk_next " & " "=" in
        let next_neq = mk_next " | " "!=" in
        fprintf out "MODULE kntr_%d(%s, %s, myval)\n"
            idx params next_params;
        fprintf out " ASSIGN\n";
        fprintf out " next(myval) :=\n";
        fprintf out "  case\n";
        let print_next k vs =
            fprintf out "   (%s) & (%s) & myval = %d : { %s };\n"
                prev_neq next_eq k (str_join ", " (List.map string_of_int vs));
        in
        let print_prev k vs =
            fprintf out "   (%s) & (%s) & myval = %d : { %s };\n"
                prev_eq next_neq k (str_join ", " (List.map string_of_int vs))
        in
        Hashtbl.iter print_prev dec_tbl;
        Hashtbl.iter print_next inc_tbl;
        fprintf out "   TRUE : myval;\n";
        fprintf out "  esac;\n";
    in
    let all_indices = ctr_ctx#all_indices_for (fun _ -> true) in
    List.iter create_module all_indices

    
let transform solver caches out_name prog =
    let out = open_out (out_name ^ ".smv") in
    List.iter (create_proc_counters solver caches out) (Program.get_procs prog);
    close_out out

