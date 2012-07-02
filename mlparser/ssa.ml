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

let mk_ssa vars cfg =
    (* initial indices assigned to variables *)
    visit_cfg (visit_basic_block (transfer_var_version (Hashtbl.create 10)))
        (join lub_var_nos) (print_var_version "ssa_vers") cfg
;;

