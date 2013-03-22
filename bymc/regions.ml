(* Keeping info about regions of a control flow graph.
 * A region is a pair of statement ids [first_id, last_id].
 * This pair defines a list of statements between two statements with
 * these distinguished identifiers. Note that statement identifiers need
 * not to be ordered. This definition is tricky when it comes to compound
 * MIR statements like if, atomic, d_step, etc.
 *
 * The good property of this representation is that adding/removing
 * statements does not affect a region (except for the first and the last
 * statements of course).
 *
 * NOTE: if one wants to change the regions when statements are modified,
 * then statements must be added only via a special interface like
 * insert_before, insert_after, remove_before, remove_after.
 *
 * Igor Konnov, 2012
 *)

open Accums
open Printf
open Spin
open SpinIr

exception Region_error of string

let rec find_region_by_range
        (first: int) (last: int) (stmts: token mir_stmt list):
        token mir_stmt list option =
    (* DEBUG:
    Printf.printf "find_region_by_range %d %d len(stmts) = %d\n"
        first last (List.length stmts);
     *)
    let rec search_in_compound = function
        | (MAtomic (_, body)) :: tl
        | (MD_step (_, body)) :: tl ->
            let found = find_region_by_range first last body in
            if is_none found
            then search_in_compound tl
            else Some (get_some found)

        | (MIf (_, options)) :: tl ->
            let found = search_in_opt options in
            if is_none found
            then search_in_compound tl
            else Some (get_some found)

        | _ :: tl -> search_in_compound tl
        
        | [] -> None

    and search_in_opt = function
        | (MOptGuarded body) :: tl
        | (MOptElse body) :: tl ->
            let found = find_region_by_range first last body in
            if is_none found
            then search_in_opt tl
            else Some (get_some found)
        
        | [] -> None
    in

    let find_pos id =
        let rec search pos = function
        | hd :: tl ->
            if (m_stmt_id hd) = id
            then pos
            else search (pos + 1) tl

        | [] -> -1
        in
        search 0 stmts
    in
    let first_pos, last_pos = (find_pos first), (find_pos last) in
    (* DEBUG:
    Printf.printf "first_pos = %d, last_pos = %d\n" first_pos last_pos;
    *)
    (* lots of diagnostics *)
    if first_pos >= 0 && last_pos < 0
    then let m = sprintf
        "Malformed region, ids %d and %d are located on different levels"
        first last in
        raise (Region_error m)
    else if first_pos > last_pos
    then raise (Region_error
        ("Malformed region, last statement before first statement"))
    else if first_pos >= 0
    (* everything is fine, return the statements *)
    then Some (list_sub stmts first_pos (last_pos - first_pos + 1))
    (* look into the compound statements *)
    else search_in_compound stmts


class region_tbl =
    object
        val null_id = -1
        val mutable m_regions: (string, int * int) Hashtbl.t =
            Hashtbl.create 5

        method add name (stmts: token mir_stmt list): unit =
            if stmts = []
            then Hashtbl.replace m_regions name (null_id, null_id)
            else let first = List.hd stmts in
                let last = List.hd (List.rev stmts) in
                Hashtbl.replace
                    m_regions name (m_stmt_id first, m_stmt_id last)

        method get name all_stmts =
            let first_id, last_id =
                try Hashtbl.find m_regions name
                with Not_found ->
                    raise (Region_error ("No region " ^ name))
            in
            if first_id = null_id
            then [] (* An empty region. Yes, it is possible. *)
            else match find_region_by_range first_id last_id all_stmts with
            | Some stmts -> stmts
            | None ->
                let m = sprintf "No region %s:[%d, %d] found"
                    name first_id last_id in
                raise (Region_error m)
    end

