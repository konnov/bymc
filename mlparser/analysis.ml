(* Analysis based on abstract interpretation *)

open Cfg;;
open Spin;;
open Spin_ir;;

(* general analysis *)
let visit_basic_block transfer_fun bb in_vals =
    List.fold_left (fun res stmt -> transfer_fun stmt res) in_vals bb#get_seq
;;

let visit_cfg visit_bb_fun join_fun cfg entry_vals =
    let bb_vals = Hashtbl.create 10 in
    Hashtbl.add bb_vals 0 entry_vals;
    let rec visit_once = function
        | [] -> []
        | hd :: tl ->
            let id = hd#get_lead_lab in
            let old_vals = Hashtbl.find bb_vals id in
            let new_vals = join_fun old_vals (visit_bb_fun hd old_vals) in
            if old_vals <> new_vals
            then begin
                Hashtbl.add bb_vals id old_vals;
                List.append tl hd#get_succ
            end
            else tl
    in
    visit_once (Hashtbl.find cfg 0)
;;

(* special kind of analysis *)
type int_role = IntervalInt of int * int | UnboundedInt | Undefined;;

let lub_int_role x y =
    match x, y with
    | Undefined, d -> d
    | d, Undefined -> d
    | UnboundedInt, _ -> UnboundedInt
    | _, UnboundedInt -> UnboundedInt
    | (IntervalInt (a, b)), (IntervalInt (c, d)) ->
        IntervalInt ((min a c), (max b  d))
;;

let join_int_roles lhs rhs =
    let res = Hashtbl.create (Hashtbl.length lhs) in
    Hashtbl.iter
        (fun var value ->
            if Hashtbl.mem rhs var
            then Hashtbl.add res var (lub_int_role value (Hashtbl.find rhs var))
            else Hashtbl.add res var value)
        lhs;
    Hashtbl.iter
        (fun var value ->
            if not (Hashtbl.mem rhs var) then Hashtbl.add res var value)
        rhs;
    res
;;

let transfer_roles stmt input =
    let output = Hashtbl.create (Hashtbl.length input)
    in
    let rec eval expr = 
        match expr with
        | Const v -> IntervalInt (v, v)
        | Var var ->
            if Hashtbl.mem input var then Hashtbl.find input var else Undefined
        | UnEx (_, _) -> Undefined
        | BinEx (ASGN, Var var, rhs) ->
            let rhs_val = eval rhs in
            Hashtbl.add output var rhs_val;
            rhs_val
        | BinEx (PLUS, lhs, rhs) -> UnboundedInt (* we are interested in == and != *)
        | BinEx (MINUS, lhs, rhs) -> UnboundedInt
        | BinEx (_, _, _) -> Undefined
        | _ -> Undefined       
    in
    begin
        match stmt with
        | Decl (var, init_expr) -> Hashtbl.add output var (eval init_expr)
        | Expr expr -> let _ = eval expr in ()
        | _ -> ()
    end;
    output
;;

