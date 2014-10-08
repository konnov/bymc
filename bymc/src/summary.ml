(** Constructing a summary similar to SymbSkel, but by enumerating SMT
    models instead of a call to NuSMV.
 
    Igor Konnov, 2014
 *)

open Printf

open Batteries

open Debug
open Smt
open Spin
open SpinIr
open SpinIrImp
open SymbSkel

(** enumerate the values of missing variables *)
(* XXX: most likely, inefficient *)
let expand_cube f ctx partial_cube =
    let leave_unbound n e l =
        match e with
        | Var v ->
                if v#get_name = n && v#proc_name <> ""
                then v :: l
                else l
        | _ -> l
    in

    let extend cube v i =
        let copy = Hashtbl.copy cube in
        Hashtbl.replace copy v#get_name (IntConst i);
        copy
    in
    let rec enum cube = function
            | [] ->
                f cube
    
            | v :: tl ->
                let orig = (ctx.SkB.sym_tab#lookup v#get_name)#as_var in
                let t = ctx.SkB.type_tab#get_type orig in
                assert (t#has_range);
                let l, r = t#range in
                let each_val i = enum (extend cube v i) tl in
                List.iter each_val (Accums.range l r)
    in
    let unbound = Hashtbl.fold leave_unbound partial_cube [] in
    enum partial_cube unbound


let mk_loc assigns v =
    let value var =
        try Hashtbl.find assigns var#get_name
        with Not_found ->
            raise (Failure ("No assignment for " ^ var#get_name))
    in
    let rec sub rank = function
        | IntConst i -> i

        | Var r ->
                if rank > 0
                then sub (rank - 1) (value r)
                else raise (Failure "Code red: inf. recursion")

        | _ as e -> raise (Failure ("expected integer, found: " ^ (expr_s e)))
    in
    sub (Hashtbl.length assigns) (value v)


let mk_act syms assigns =
    let add name exp l =
        try let var = (syms#lookup name)#as_var in
            if var#proc_name <> ""
            then l (* omit local variables *)
            else (BinEx (EQ, UnEx (NEXT, Var var), exp)) :: l
        with Symbol_not_found _ -> l
    in
    Hashtbl.fold add assigns []


let enum_cubes rt ctx used vars cons assigns =
    let decl v = rt#solver#append_var_def v (ctx.SkB.type_tab#get_type v) in
    let simp val_fun e = map_vars val_fun e |> Simplif.compute_consts in
    let add_rule val_fun cube =
        let prev_loc =
            List.map ((mk_loc cube) % fst) ctx.SkB.prev_next
                |> SkB.add_loc ctx.SkB.state 
        in
        let next_loc =
            List.map ((mk_loc cube) % snd) ctx.SkB.prev_next
                |> SkB.add_loc ctx.SkB.state 
        in
        let acts = mk_act ctx.SkB.sym_tab cube in
        let rule = { Sk.src = prev_loc; Sk.dst = next_loc;
                     Sk.guard = simp val_fun cons; Sk.act = acts }
        in
        ignore (SkB.add_rule ctx.SkB.state rule)
    in

    if is_c_true cons
    then begin
        (* no constraints at all except probably those from the assignments *)
        let get_val v = Var v in
        expand_cube (add_rule get_val) ctx assigns
    end else begin
        (* enumerate all models that satisfy the path constraint *)
        rt#solver#push_ctx;
        rt#solver#set_need_model true;
        List.iter decl used;
        rt#solver#append_expr cons;

        while rt#solver#check do
            let vals = Hashtbl.create (List.length vars) in
            let get_val v =
                if Hashtbl.mem vals v then Hashtbl.find vals v else Var v in
            let each q v =
                match Q.try_get q (Var v) with
                | Q.Cached -> ()
                | Q.Result e ->
                        Hashtbl.replace vals v e;
            in
            let query = rt#solver#get_model_query in
            List.iter (each query) vars;
            let new_query = rt#solver#submit_query query in
            List.iter (each new_query) vars;
            let cube = Hashtbl.map (fun _ e -> simp get_val e) assigns in
            trace Trc.sum (fun _ ->
                let p n v = printf "    %s <- %s\n" n (SpinIrImp.expr_s v) in
                Hashtbl.iter p cube;
                sprintf "  simp_cons: %s\n  simp_vars:\n"
                    (expr_s (simp get_val cons))
            );

            (* if the cube is a partial assignment, enumerate all assignments *)
            expand_cube (add_rule get_val) ctx cube;

            let neqs =
                Hashtbl.fold (fun v e l -> (BinEx (NE, Var v, e)) :: l) vals []
            in
            rt#solver#append_expr (list_to_binex OR neqs)
        done;
        rt#solver#set_need_model false;
        rt#solver#pop_ctx
    end


let each_path rt ctx cons vals =
    let used = SpinIr.expr_used_vars cons in
    let locals = List.filter (fun v -> v#proc_name <> "") used in
    enum_cubes rt ctx used locals cons vals;
    trace Trc.sum (fun _ ->
        let p n v = printf "  %s <- %s\n" n (SpinIrImp.expr_s v) in
        Hashtbl.iter p vals;
        sprintf "cons: %s\n" (SpinIrImp.expr_s cons))


let summarize rt prog proc =
    build_with (each_path rt) rt prog proc


