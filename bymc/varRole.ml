open Printf

open Accums
open Analysis
open Cfg
open Debug
open SkelStruc
open Spin
open SpinIr
open SpinIrImp

type var_role =
    BoundedInt of int * int | SharedUnbounded | LocalUnbounded | Scratch

let var_role_s r =
    match r with
    | BoundedInt (a, b) -> Printf.sprintf "bounded[%d, %d]" a b
    | SharedUnbounded -> "shared-unbounded"
    | LocalUnbounded -> "local-unbounded"
    | Scratch -> "scratch"

let is_unbounded = function
    | SharedUnbounded
    | LocalUnbounded -> true
    | _ -> false

let is_bounded = function
    | BoundedInt (_, _) -> true
    | _ -> false

let is_local_unbounded = function
    | LocalUnbounded -> true
    | _ -> false

let is_shared_unbounded = function
    | SharedUnbounded -> true
    | _ -> false

exception Role_error of string
exception Var_not_found of string


class var_role_tbl (i_roles: (var, var_role) Hashtbl.t) =
    object
        method get_role v =
            try Hashtbl.find i_roles v
            with Not_found -> raise (Var_not_found v#get_name)

        method get_all = i_roles
    end


let identify_var_roles prog =
    let roles = Hashtbl.create 10 in
    let fill_roles proc =
        let cfg = Cfg.mk_cfg (mir_to_lir proc#get_stmts) in
        let (int_roles: (int, (var, int_role) Hashtbl.t) Hashtbl.t) =
            visit_cfg (visit_basic_block transfer_roles)
                (join lub_int_role) (print_int_roles "roles") cfg in
        let body_sum =
            join_all_locs (join lub_int_role) (mk_bottom_val ()) int_roles in
        let reg_tab = extract_skel proc#get_stmts in
        let fst_id =
            let is_norm s = (m_stmt_id s) <> -1 in
            (m_stmt_id (List.find is_norm (reg_tab#get "comp"))) in
        let loc_roles =
            try Hashtbl.find int_roles fst_id
            with Not_found ->
                let m = (sprintf "No analysis data for loc %d" fst_id) in
                raise (Failure m)
        in
        Hashtbl.iter
            (fun v r ->
                let is_const = match Hashtbl.find loc_roles v with
                    | IntervalInt (a, b) -> a = b   (* const *)
                    | _ -> false                    (* mutating *)
                in
                let new_role = if is_const
                then Scratch
                else match Hashtbl.find body_sum v with
                    | IntervalInt (a, b) -> BoundedInt (a, b)
                    | UnboundedInt -> LocalUnbounded
                    | Undefined ->
                        raise (Role_error
                            (sprintf "Undefined type for %s" v#get_name))
                in
                Hashtbl.replace roles v new_role (* XXX: can we lose types? *)
            ) body_sum;
    in
    List.iter fill_roles (Program.get_procs prog);

    let replace_global v =
        if LocalUnbounded <> (Hashtbl.find roles v)
        then raise (Role_error
            (sprintf "Shared variable %s is bounded" v#get_name))
        else Hashtbl.replace roles v SharedUnbounded
    in
    List.iter replace_global (Program.get_shared prog);

    log INFO " # Variable roles:";
    let sorted = List.sort cmp_qual_vars (hashtbl_keys roles) in
    let print_var_role v =
        let r = Hashtbl.find roles v in
        log INFO (sprintf "   %s -> %s" v#qual_name (var_role_s r)) in
    List.iter print_var_role sorted;

    new var_role_tbl roles

