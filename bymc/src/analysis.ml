(* Very simple analysis based on abstract interpretation *)

open Printf

open Cfg
open Spin
open SpinIr
open SpinIrImp
open Debug

exception Analysis_error of string

(* general analysis *)
let mk_bottom_val () = Hashtbl.create 10 

let visit_basic_block transfer_fun stmt_vals bb in_vals =
    let transfer_stmt input stmt =
        Hashtbl.replace stmt_vals (stmt_id stmt) input;
        transfer_fun stmt input
    in
    List.fold_left transfer_stmt in_vals bb#get_seq


let visit_cfg visit_bb_fun join_fun print_fun cfg =
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
                (in_vals, true)
        in
        if changed
        then begin
            log DEBUG ("ELEM CHANGED, PROPAGATING RESULTS");
            log DEBUG "INPUT: "; (print_fun new_vals);
            Hashtbl.replace bb_vals id new_vals;
            let out_vals = (visit_bb_fun stmt_vals basic_blk new_vals) in
            log DEBUG "OUTPUT: "; (print_fun out_vals);
            let next = List.map (fun bb_s -> (bb_s, out_vals)) basic_blk#get_succ
            in
            log DEBUG (sprintf "#SUCCS: %d" (List.length next));
            next
        end
        else [] (* nothing more to process *)
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


let join_all_locs join_fun init_vals loc_vals =
    Hashtbl.fold (fun _ vals sum -> join_fun sum vals) loc_vals init_vals 


(* special kinds of analysis *)

(* int or bounded int *)
type int_role = IntervalInt of int * int | UnboundedInt | Undefined

let int_role_s = function
    | IntervalInt (a, b) -> sprintf "[%d, %d]" a b
    | UnboundedInt -> "unbounded"
    | Undefined -> "undefined"


let lub_int_role x y =
    match x, y with
    | Undefined, d -> d
    | d, Undefined -> d
    | UnboundedInt, _ -> UnboundedInt
    | _, UnboundedInt -> UnboundedInt
    | (IntervalInt (a, b)), (IntervalInt (c, d)) ->
        IntervalInt ((min a c), (max b  d))


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


type var_use = VarUses of VarSet.t | VarUsesUndef


let var_use_s = function
    | VarUses vars ->
            let names = List.map (fun v -> v#get_name) (VarSet.elements vars) in
            "{" ^ (Accums.str_join ", " names) ^ "}"
    | VarUsesUndef ->
            "{}"


let lub_var_use x y =
    match x, y with
    | VarUsesUndef, VarUses vs -> VarUses vs
    | VarUses vs, VarUsesUndef -> VarUses vs
    | VarUses vs1, VarUses vs2 -> VarUses (VarSet.union vs1 vs2)
    | VarUsesUndef, VarUsesUndef -> VarUsesUndef


let print_var_uses head vals =
    if may_log DEBUG
    then begin
        printf " %s { " head;
        Hashtbl.iter
            (fun var aval -> printf "%s: %s; "
                var#get_name (var_use_s aval))
            vals;
        printf "}\n";
    end


let join lub_fun lhs rhs =
    let res = Hashtbl.create (Hashtbl.length lhs) in
    Hashtbl.iter
        (fun var value ->
            let newv = if Hashtbl.mem rhs var
            then (lub_fun value (Hashtbl.find rhs var))
            else value in
            Hashtbl.add res var newv
        ) lhs;
    Hashtbl.iter
        (fun var value ->
            if not (Hashtbl.mem res var) then Hashtbl.add res var value
        ) rhs;
    res


let transfer_roles stmt input =
    log DEBUG (sprintf "  %%%s;" (stmt_s stmt));
    let output = Hashtbl.copy input
    in
    let rec eval = function
        | IntConst v -> IntervalInt (v, v)
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
        | Havoc (_, v) ->
            Hashtbl.replace output v UnboundedInt;
        | _ -> ()
    end;
    print_int_roles "input = " input;
    print_int_roles "output = " output;
    output


let transfer_var_use stmt input =
    log DEBUG (sprintf "  %%%s;" (stmt_s stmt));
    let output = Hashtbl.copy input
    in
    let rec eval = function
        | IntConst v ->
            VarUsesUndef
        | Var var ->
            VarUses (VarSet.add var VarSet.empty)
        | UnEx (_, e) ->
            eval e
        | BinEx (ASGN, Var var, rhs) ->
            let rhs_val = eval rhs in
            Hashtbl.replace output var rhs_val;
            rhs_val
        | BinEx (_, lhs, rhs) ->
            lub_var_use (eval lhs) (eval rhs)
        | _ -> VarUsesUndef
    in
    begin
        match stmt with
        | Decl (_, var, init_expr) ->
                Hashtbl.replace output var (eval init_expr)
        | Expr (_, expr) ->
                let _ = eval expr in ()
        | _ -> ()
    end;
    output


let var_used_by uses target =
    let check_use host host_uses set =
        match host_uses with
        | VarUses s ->
            if VarSet.mem target s then VarSet.add host set else set
        | _ -> set
    in
    Hashtbl.fold check_use uses VarSet.empty


(*
  Find assignments like: x = y.
 *)
let find_copy_pairs stmts =
    let pairs = Hashtbl.create 8 in
    let extract = function
        | Expr (_, BinEx (ASGN, Var x, Var y)) ->
            if Hashtbl.mem pairs x
            then raise (Failure ("Two copy pairs for " ^ x#get_name))
            else Hashtbl.add pairs x y
        | _ -> ()
    in
    List.iter extract stmts;
    pairs

