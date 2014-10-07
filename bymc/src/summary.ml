(** Constructing a summary similar to SymbSkel, but by enumerating SMT
    models instead of a call to NuSMV.
 
    Igor Konnov, 2014
 *)

open Printf

open Batteries

open Smt
open Spin
open SpinIr
open SpinIrImp
open SymbSkel

let mk_loc assigns f pair =
    let name = (f pair)#get_name in
    let value =
        try Hashtbl.find assigns name
        with Not_found ->
            raise (Failure ("No assignment for " ^ name))
    in
    match value with
    | IntConst i -> i
    | _ -> raise (Failure "expected integer")


let mk_act syms assigns =
    let add name exp l =
        try let var = (syms#lookup name)#as_var in
            begin
                match exp with
                | Var x ->
                        if x#get_name = var#get_name
                        then l
                        else (BinEx (EQ, UnEx (NEXT, Var var), exp)) :: l
                
                | _ -> (BinEx (EQ, UnEx (NEXT, Var var), exp)) :: l
            end
        with Symbol_not_found _ -> l
    in
    Hashtbl.fold add assigns []


let enum_cubes rt ctx used vars cons assigns =
    let decl v = rt#solver#append_var_def v (ctx.SkB.type_tab#get_type v) in
    rt#solver#push_ctx;
    rt#solver#set_need_model true;
    List.iter decl used;
    rt#solver#append_expr cons;
    while rt#solver#check do
        let vals = Hashtbl.create (List.length vars) in
        let each q v =
            match Q.try_get q (Var v) with
            | Q.Cached -> ()
            | Q.Result e ->
                    Hashtbl.replace vals v e;
                    printf "  %s <- %s\n" v#get_name (expr_s e)
        in
        let query = rt#solver#get_model_query in
        List.iter (each query) vars;
        let new_query = rt#solver#submit_query query in
        List.iter (each new_query) vars;
        let get_val v =
            if Hashtbl.mem vals v then Hashtbl.find vals v else Var v in
        let simp e = map_vars get_val e |> Simplif.compute_consts in
        let cube = Hashtbl.map (fun _ e -> simp e) assigns in
        (*
        printf "  simp_cons: %s\n  simp_vars:\n" (expr_s (simp cons));
        let p n v = printf "    %s <- %s\n" n (SpinIrImp.expr_s v) in
        Hashtbl.iter p cube;
        *)
        let prev_loc =
            SkB.add_loc ctx.SkB.state (List.map (mk_loc cube fst) ctx.SkB.prev_next) in
        let next_loc =
            SkB.add_loc ctx.SkB.state (List.map (mk_loc cube snd) ctx.SkB.prev_next) in
        let acts = mk_act ctx.SkB.sym_tab cube in
        let rule = { Sk.src = prev_loc; Sk.dst = next_loc;
                     Sk.guard = simp cons; Sk.act = acts }
        in
        ignore (SkB.add_rule ctx.SkB.state rule);

        let neqs =
            Hashtbl.fold (fun v e l -> (BinEx (NE, Var v, e)) :: l) vals []
        in
        rt#solver#append_expr (list_to_binex OR neqs)
    done;
    rt#solver#set_need_model false;
    rt#solver#pop_ctx


let each_path rt ctx cons vals =
    let used = SpinIr.expr_used_vars cons in
    let locals = List.filter (fun v -> v#proc_name <> "") used in
    enum_cubes rt ctx used locals cons vals
    (*
    let p n v = printf "  %s <- %s\n" n (SpinIrImp.expr_s v) in
    printf "cons: %s\n" (SpinIrImp.expr_s cons);
    Hashtbl.iter p vals
    *)


let summarize rt prog proc =
    let skel, _ = build_with (each_path rt) rt prog proc in
    skel


