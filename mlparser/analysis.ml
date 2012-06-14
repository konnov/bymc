(* Analysis based on abstract interpretation *)

open Printf;;

open Cfg;;
open Spin;;
open Spin_ir;;
open Spin_ir_imp;;
open Debug;;

exception Analysis_error of string;;

(* general analysis *)
let mk_bottom_val () = Hashtbl.create 10 ;;

let visit_basic_block transfer_fun stmt_vals bb in_vals =
    let transfer_stmt input stmt =
        Hashtbl.replace stmt_vals (stmt_id stmt) input;
        transfer_fun stmt input
    in
    List.fold_left transfer_stmt in_vals bb#get_seq
;;

let visit_cfg visit_bb_fun join_fun cfg entry_vals =
    (* imperative because of Hahstbl :-( *)
    let bb_vals = Hashtbl.create 10 in
    let stmt_vals = Hashtbl.create 10 in
    let visit_once (basic_blk, in_vals) = 
        let id = basic_blk#get_lead_lab in
        let new_vals, changed =
            try
                let oldv = Hashtbl.find bb_vals id in
                let newv = join_fun oldv in_vals in
                (newv, not (Accums.hashtbl_eq oldv newv))
            with Not_found ->
                (mk_bottom_val (), true)
        in
        if changed
        then begin
            Hashtbl.replace bb_vals id new_vals;
            let out_vals = (visit_bb_fun stmt_vals basic_blk new_vals) in
            List.map (fun s -> (s, out_vals)) basic_blk#get_succ
        end
        else []
    in
    let rec visit = function
        | [] -> ()
        | hd :: tl ->
            let next_open = visit_once hd in
            visit tl; visit next_open
    in
    visit (Hashtbl.fold
        (fun _ bb lst -> (bb, mk_bottom_val ()) :: lst)
        cfg#blocks []);
    stmt_vals
;;

let join_all_locs join_fun init_vals loc_vals =
    Hashtbl.fold (fun _ vals sum -> join_fun sum vals) loc_vals init_vals 
;;

(* special kinds of analysis *)

(* int or bounded int *)
type int_role = IntervalInt of int * int | UnboundedInt | Undefined;;

let int_role_s = function
    | IntervalInt (a, b) -> sprintf "[%d, %d]" a b
    | UnboundedInt -> "unbounded"
    | Undefined -> "undefined"
;;

let lub_int_role x y =
    match x, y with
    | Undefined, d -> d
    | d, Undefined -> d
    | UnboundedInt, _ -> UnboundedInt
    | _, UnboundedInt -> UnboundedInt
    | (IntervalInt (a, b)), (IntervalInt (c, d)) ->
        IntervalInt ((min a c), (max b  d))
;;

let print_int_roles head vals =
    if may_log DEBUG
    then begin
        printf " %s { " head;
        Hashtbl.iter
            (fun var aval -> printf "%s: %s; "
                var#get_name (int_role_s aval))
            vals;
        printf "}\n";
    end
;;

let join_int_roles lhs rhs =
    let res = Hashtbl.create (Hashtbl.length lhs) in
    Hashtbl.iter
        (fun var value ->
            if Hashtbl.mem rhs var
            then Hashtbl.replace res var (lub_int_role value (Hashtbl.find rhs var))
            else Hashtbl.add res var value)
        lhs;
    Hashtbl.iter
        (fun var value ->
            if not (Hashtbl.mem res var) then Hashtbl.add res var value)
        rhs;
    print_int_roles " join = " res;
    res
;;

let transfer_roles stmt input =
    log DEBUG (sprintf "  %%%s;" (stmt_s stmt));
    let output = Hashtbl.copy input
    in
    let rec eval = function
        | Const v -> IntervalInt (v, v)
        | Var var ->
            if Hashtbl.mem input var then Hashtbl.find input var else Undefined
        | UnEx (_, _) -> Undefined
        | BinEx (ASGN, Var var, rhs) ->
            let rhs_val = eval rhs in
            Hashtbl.replace output var rhs_val;
            rhs_val
        | BinEx (PLUS, lhs, rhs) -> UnboundedInt (* we are interested in == and != *)
        | BinEx (MINUS, lhs, rhs) -> UnboundedInt
        | BinEx (_, _, _) -> Undefined
        | _ -> Undefined       
    in
    begin
        match stmt with
        | Decl (_, var, init_expr) ->
                Hashtbl.replace output var (eval init_expr)
        | Expr (_, expr) ->
                let _ = eval expr in ()
        | _ -> ()
    end;
    print_int_roles "input = " input;
    print_int_roles "output = " output;
    output
;;

(*
  Find assignments like: x = y.
 *)
let find_copy_pairs stmts =
    let pairs = Hashtbl.create 8 in
    List.iter
        (function
            | Expr (_, BinEx (ASGN, Var x, Var y)) ->
                    Hashtbl.add pairs x y
            | _ -> ()
        ) stmts;
    pairs
;;
