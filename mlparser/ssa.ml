(* Single static assignment form *)

open Printf;;

open Cfg;;
open Analysis;;
open Spin;;
open Spin_ir;;
open Spin_ir_imp;;
open Debug;;

type var_nos = int list;; (* a list of identifiers assigned to a var in a loc *)

let lub_var_nos (x: int list) (y: int list) : int list =
    let y_minus_x = List.filter (fun i -> not (List.mem i x)) y in
    x @ y_minus_x
;;

let var_nos_s ns =
    String.concat ", " (List.map string_of_int ns)
;;

let print_nos head vals =
    if may_log DEBUG
    then begin
        printf " %s { " head;
        Hashtbl.iter
            (fun var aval -> printf "%s: [%s]; " var#get_name (var_nos_s aval))
            vals;
        printf "}\n";
    end
;;

let transfer_nos stmt input =
    log DEBUG (sprintf "  %%%s;" (stmt_s stmt));
    let output = Hashtbl.copy input
    in
    begin
        match stmt with
        | Decl (_, v, i) ->
                Hashtbl.replace output v [0]
        | Expr (_, BinEx (ASGN, Var v, _)) ->
                begin
                try
                    let nos = Hashtbl.find input v in
                    let new_no = 1 + (List.fold_left max 0 nos) in
                    Hashtbl.replace output v [new_no]
                with Not_found -> ()
                    (* raise (Failure (sprintf "Not found %s" v#get_name))
                    *)
                end
        | _ -> ()
    end;
    print_nos "#s input = " input;
    print_nos "#s output = " output;
    output
;;

let mk_ssa vars cfg =
    (* initial indices assigned to variables *)
    visit_cfg (visit_basic_block transfer_nos)
        (join lub_var_nos) (print_nos "ssa_nums") cfg
;

