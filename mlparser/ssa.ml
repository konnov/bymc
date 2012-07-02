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
        let children = Hashtbl.find idom_tree node in
        List.iter bottom_up children;
        visit_node node
    in
    bottom_up 0;
    df
;;

let mk_ssa vars cfg =
    (* initial indices assigned to variables *)
    visit_cfg (visit_basic_block (transfer_var_version (Hashtbl.create 10)))
        (join lub_var_nos) (print_var_version "ssa_vers") cfg
;

