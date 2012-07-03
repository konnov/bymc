(* Single static assignment form *)

open Printf;;

open Cfg;;
open Analysis;;
open Spin;;
open Spin_ir;;
open Spin_ir_imp;;
open Debug;;

(* variable versions assigned to a location *)
type var_version = { out_ver: int; in_vers: int list }

let lub_var_nos (x: var_version) (y: var_version) : var_version =
    let y_minus_x = List.filter (fun i -> not (List.mem i x.in_vers)) y.in_vers
    in
    { out_ver = (max x.out_ver y.out_ver); in_vers = (x.in_vers @ y_minus_x) }
;;

let var_version_s v =
    (sprintf "%s -> %d"
        (String.concat ", " (List.map string_of_int v.in_vers)) v.out_ver)
;;

let print_var_version head vals =
    if may_log DEBUG
    then begin
        printf " %s { " head;
        Hashtbl.iter
            (fun var aval -> printf "%s: [%s]; " var#get_name (var_version_s aval))
            vals;
        printf "}\n";
    end
;;

let transfer_var_version tbl stmt input =
    log DEBUG (sprintf "  %%%s;" (stmt_s stmt));
    let output = Hashtbl.create (Hashtbl.length input) in
    let copy_elem var ver =
        if ver.out_ver = -1
        then Hashtbl.add output var ver
        else Hashtbl.add output var { out_ver = -1; in_vers = [ver.out_ver] }
    in
    Hashtbl.iter copy_elem input;
    begin
        match stmt with
        | Decl (id, v, i) ->
                Hashtbl.add tbl id 0;
                Hashtbl.replace output v { out_ver = 0; in_vers = [] }
        | Expr (id, BinEx (ASGN, Var v, _)) ->
                begin
                try
                    let ver = Hashtbl.find input v in
                    let o_v =
                        try Hashtbl.find tbl id
                        with Not_found ->
                            let ver = Hashtbl.length tbl in
                            Hashtbl.add tbl id ver;
                            ver
                    in
                    let i_v = if ver.out_ver <> -1
                    then [ver.out_ver]
                    else ver.in_vers in
                    Hashtbl.replace output v { out_ver = o_v; in_vers = i_v }
                with Not_found -> ()
                end
        | _ -> ()
    end;
    print_var_version "#s input = " input;
    print_var_version "#s output = " output;
    output
;;

let comp_dom_frontiers cfg =
    let df = Hashtbl.create (Hashtbl.length cfg#blocks) in
    let idom_tbl = comp_idoms cfg in
    let idom_tree = comp_idom_tree idom_tbl in
    let visit_node n =
        let visit_y s df_n =
            if n <> (Hashtbl.find idom_tbl s)
            then IntSet.add s df_n
            else df_n in
        let df_n = List.fold_right visit_y (cfg#find n)#succ_labs IntSet.empty 
        in
        let propagate_up df_n z =
            IntSet.fold visit_y (Hashtbl.find df z) df_n in
        let children = Hashtbl.find idom_tree n in
        let df_n = List.fold_left propagate_up df_n children in
        Hashtbl.add df n df_n
    in
    let rec bottom_up node =
        try
            let children = Hashtbl.find idom_tree node in
            List.iter bottom_up children;
            visit_node node
        with Not_found ->
            raise (Failure (sprintf "idom children of %d not found" node))
    in
    bottom_up 0;
    df
;;

(* Ron Cytron et al. Static Single Assignment Form and the Control
   Dependence Graph, ACM Transactions on PLS, Vol. 13, No. 4, 1991, pp. 451-490.

   Figure 11.
 *)
let place_phi (vars: var list) (cfg: 't control_flow_graph) =
    let df = comp_dom_frontiers cfg in
    let iter_cnt = ref 0 in
    let has_already = Hashtbl.create (Hashtbl.length cfg#blocks) in
    let work = Hashtbl.create (Hashtbl.length cfg#blocks) in
    let init_node n =
        Hashtbl.add has_already n 0; Hashtbl.add work n 0 in
    List.iter init_node cfg#block_labs;

    let for_var v =
        let does_stmt_uses_var = function
            | Expr (_, BinEx (ASGN, Var v, _)) -> true
            | _ -> false in
        let does_blk_uses_var bb =
            List.exists does_stmt_uses_var bb#get_seq in
        let blks_using_v =
            List.map bb_lab (List.filter does_blk_uses_var cfg#block_list) in
        iter_cnt := !iter_cnt + 1;
        List.iter (fun bb -> Hashtbl.replace work bb !iter_cnt) blks_using_v;
        let work_list = ref blks_using_v in
        let one_step x =
            let do_y y = 
                if (Hashtbl.find has_already y) < !iter_cnt
                then begin
                    let bb = cfg#find y in
                    let num_preds = (List.length bb#get_pred) in
                    let phi = Expr (-1, Phi (v, Accums.n_copies num_preds v)) in
                    let seq = bb#get_seq in
                    bb#set_seq ((List.hd seq) :: phi :: (List.tl seq));
                    Hashtbl.replace has_already y !iter_cnt;
                    if (Hashtbl.find work y) < !iter_cnt
                    then begin
                        Hashtbl.replace work y !iter_cnt;
                        work_list := y :: !work_list
                    end
                end
            in
            IntSet.iter do_y (Hashtbl.find df x)
        in
        let rec many_steps () =
            match !work_list with
            | hd :: tl -> work_list := tl; one_step hd; many_steps ()
            | [] -> ()
        in
        work_list := blks_using_v;
        many_steps ()
    in
    List.iter for_var vars;
    cfg
;;

let map_rhs map_fun ex =
    let rec sub = function
    | Var v -> map_fun v
    | UnEx (t, l) -> UnEx (t, sub l)
    | BinEx (ASGN, l, r) -> BinEx (ASGN, l, sub r)
    | BinEx (t, l, r) -> BinEx (t, sub l, sub r)
    | _ as e -> e
    in
    sub ex
;;

(*
 It appears that the Cytron's algorithm can produce phi functions like
 x_2 = phi(x_1, x_1, x_1).
 Here we remove them.
 *)
let optimize_ssa cfg =
    let sub_tbl = Hashtbl.create 10 in
    let changed = ref true in
    let collect_replace bb =
        let on_stmt = function
            | Expr (id, Phi (lhs, rhs)) as s ->
                    let fst = List.hd rhs in
                    if List.for_all (fun o -> o#get_name = fst#get_name) rhs
                    then begin
                        Hashtbl.add sub_tbl lhs#get_name fst;
                        changed := true;
                        Skip id 
                    end else s
            | Expr (id, e) ->
                    let sub v =
                        if Hashtbl.mem sub_tbl v#get_name
                        then Var (Hashtbl.find sub_tbl v#get_name)
                        else Var v in
                    let ne = map_rhs sub e in
                    Expr (id, ne)
            | _ as s -> s
        in
        bb#set_seq (List.map on_stmt bb#get_seq);
    in
    while !changed do
        changed := false;
        List.iter collect_replace cfg#block_list;
    done;
    cfg
;;

(* Ron Cytron et al. Static Single Assignment Form and the Control
   Dependence Graph, ACM Transactions on PLS, Vol. 13, No. 4, 1991, pp. 451-490.

   Figure 12.
 *)
let mk_ssa shared_vars local_vars cfg =
    let vars = shared_vars @ local_vars in
    let cfg = place_phi vars cfg in
    let idom_tbl = comp_idoms cfg in
    let idom_tree = comp_idom_tree idom_tbl in

    let counters = Hashtbl.create (List.length vars) in
    let stacks = Hashtbl.create (List.length vars) in
    let nm v = v#get_name in
    let s_top v =
        let stack = Hashtbl.find stacks (nm v) in
        if stack <> []
        then List.hd stack
        else raise (Failure ("Stack is empty for " ^ v#get_name))
    in
    let s_push v i =
        Hashtbl.replace stacks (nm v) (i :: (Hashtbl.find stacks (nm v))) in
    let s_pop var_nm = 
        Hashtbl.replace stacks var_nm (List.tl (Hashtbl.find stacks var_nm)) in
    (* initialize local variables *)
    List.iter (fun v -> Hashtbl.add counters (nm v) 0) local_vars;
    List.iter (fun v -> Hashtbl.add stacks (nm v) []) local_vars;
    (* global vars are different,
       they have a first version x_0 at the initial state *)
    List.iter (fun v -> Hashtbl.add counters (nm v) 1) shared_vars;
    List.iter (fun v -> Hashtbl.add stacks (nm v) [0]) shared_vars;

    let sub_var v = new var (sprintf "%s$%d" (nm v) (s_top v)) in
    let sub_var_as_var v = Var (sub_var v) in
    let intro_var v =
        try
            let i = Hashtbl.find counters (nm v) in
            let new_v = new var (sprintf "%s$%d" (nm v) i) in
            s_push v i;
            Hashtbl.replace counters (nm v) (i + 1);
            new_v
        with Not_found ->
            raise (Failure ("Var not found: " ^ v#get_name))
    in
    let rec search x =
        let bb = cfg#find x in
        let bb_old_seq = bb#get_seq in
        let replace_rhs = function
            | Decl (id, v, e) ->
                    Decl (id, v, map_rhs sub_var_as_var e)
            | Expr (id, e) as s ->
                begin
                    try
                        let new_e = map_rhs sub_var_as_var e in
                        Expr (id, new_e)
                    with Not_found ->
                        s (* ignore other variables *)
                end
            | _ as s -> s
        in
        let replace_lhs = function
            | Decl (id, v, e) -> Decl (id, (intro_var v), e)
            | Expr (id, BinEx (ASGN, Var v, rhs)) ->
                    Expr (id, BinEx (ASGN, Var (intro_var v), rhs))
            | Expr (id, Phi (v, rhs)) ->
                    Expr (id, Phi (intro_var v, rhs))
            | _ as s -> s
        in
        let on_stmt lst s = (replace_lhs (replace_rhs s)) :: lst in
        bb#set_seq (List.rev (List.fold_left on_stmt [] bb#get_seq));
        (* put the variables in the successors *)
        let sub_phi_arg y =
            let succ_bb = cfg#find y in
            let j = Accums.list_find_pos x succ_bb#pred_labs in
            let on_phi = function
            | Expr (id, Phi (v, rhs)) ->
                let (before, e, after) = Accums.list_nth_slice rhs j in
                let new_e = sub_var e in
                Expr (id, Phi (v, before @ (new_e :: after)))
            | _ as s -> s
            in
            succ_bb#set_seq (List.map on_phi succ_bb#get_seq)
        in
        List.iter sub_phi_arg bb#succ_labs;
        (* visit children in the dominator tree *)
        List.iter search (Hashtbl.find idom_tree x);
        (* pop the stack for each assignment *)
        let pop_v v = s_pop v#get_name in
        let pop_stmt = function
            | Decl (_, v, _) -> pop_v v
            | Expr (_, Phi (v, _)) -> pop_v v
            | Expr (_, BinEx (ASGN, Var v, _)) -> pop_v v
            | _ -> ()
        in
        List.iter pop_stmt bb_old_seq
    in
    search 0;
    optimize_ssa cfg (* optimize it after all *)
;;

