(* Encode regular expressions on paths and check them with an SMT solver.
 *
 * Igor Konnov, 2014
 *)

open Printf

open Accums
open PorBounds
open SpinIr
open SymbSkel

(* A single frame that corresponds to a state in a path *)
module F = struct
    type frame_t = {
        no: int; (* sequential number of the frame *)
        loc_vars: var list; (* one copy per location *)
        shared_vars: var list; (* one copy per shared variable *)
        new_vars: var list;
            (*  the variables (from loc_vars and shared_vars)
                introduced in this frame  *)
        var_map: var IntMap.t;
            (* mapping id of the original variable to its copy in the frame *)
    }

    let mk_loc_var (tt: data_type_tab) frame_no proto =
        let nv = proto#copy (sprintf "F%d_at_%s" frame_no proto#get_name) in
        tt#set_type nv (tt#get_type proto);
        nv


    let mk_shared_var (tt: data_type_tab) frame_no proto =
        let nv = proto#copy (sprintf "F%d_g_%s" frame_no proto#get_name) in
        tt#set_type nv (tt#get_type proto);
        nv

        (* TODO: myself 2015, please write a comment! *)
    let advance_frame tt sk prev_frame is_var_updated_fun =
        let copy_var ctor_fun (map, vs, new_vs) basev v =
            if is_var_updated_fun v
            then let nv = ctor_fun tt (1 + prev_frame.no) basev in
                (IntMap.add basev#id nv map, nv :: vs, nv :: new_vs)
            else (map, v :: vs, new_vs)
        in
        let loc_vars = List.map (Sk.locvar sk) (range 0 sk.Sk.nlocs) in
        let map, locs, new_vars =
            List.fold_left2 (copy_var mk_loc_var) (prev_frame.var_map, [], [])
                (List.rev loc_vars) (List.rev prev_frame.loc_vars) in
        let map, shared, new_vars =
            List.fold_left2 (copy_var mk_shared_var)
                (map, [], new_vars) (List.rev sk.Sk.shared) (List.rev prev_frame.shared_vars) in 
        { no = 1 + prev_frame.no; loc_vars = locs; shared_vars = shared;
            new_vars = new_vars; var_map = map }

    let init_frame tt sk =
        let loc_vars = List.map (Sk.locvar sk) (range 0 sk.Sk.nlocs) in
        let empty_frame = {
            no = -1; loc_vars = loc_vars; shared_vars = sk.Sk.shared;
            new_vars = []; var_map = IntMap.empty
        }
        in
        advance_frame tt sk empty_frame (fun v -> true)

    let map_frame_vars frame nframe expr =
        let map_var fr v =
            if IntMap.mem v#id fr.var_map
            then Var (IntMap.find v#id fr.var_map)
            else Var v
        in
        let rec sub = function
            | Var v -> map_var frame v
            | UnEx (Spin.NEXT, Var v) -> map_var nframe v
            | UnEx (t, e) -> UnEx (t, sub e)
            | BinEx (t, l, r) -> BinEx (t, sub l, sub r)
            | _ as e -> e
        in
        sub expr
            

    let declare_frame solver tt frame =
        solver#comment (sprintf "frame %d" frame.no);
        let add_var v =
            solver#append_var_def v (tt#get_type v) in
        List.iter add_var frame.new_vars

    let assert_frame solver tt frame next_frame assertions =
        let add_expr e =
            ignore (solver#append_expr (map_frame_vars frame frame e)) in
        List.iter add_expr assertions

end

let encode_path_elem rt tt sk start_frame pathelem =
    let each_rule frame rule_no =
        let is_new_f v =
            true
        in
        let new_frame = F.advance_frame tt sk frame is_new_f in
        F.declare_frame rt#solver tt new_frame;
        let rule = List.nth sk.Sk.rules rule_no in
        F.assert_frame rt#solver tt frame new_frame
            (* TODO: acceleration factor *)
            (* TODO: guard must label only the milestones *)
            (rule.Sk.guard :: rule.Sk.act);
        new_frame       
    in
    let each_path_elem = function
    | MaybeMile (_, _) -> start_frame
    | Seg rules -> List.fold_left each_rule start_frame rules
    in
    each_path_elem pathelem


let check_path rt tt sk path =
    rt#solver#push_ctx;
    let ntt = tt#copy in
    let initf = F.init_frame ntt sk in
    F.declare_frame rt#solver ntt initf;
    F.assert_frame rt#solver ntt initf initf sk.Sk.inits;
    let lastf = List.fold_left (encode_path_elem rt tt sk) initf path in
    rt#solver#pop_ctx;
    false

