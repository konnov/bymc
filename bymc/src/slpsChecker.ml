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

    let init_frame tt sk =
        let copy_var f (map, vs) v =
            let nv = f tt 0 v in
            (IntMap.add v#id nv map, nv :: vs)
        in
        let loc_vars =
            List.rev (List.map (Sk.locvar sk) (range 0 sk.Sk.nlocs)) in
        let map, locs =
            List.fold_left (copy_var mk_loc_var)
                (IntMap.empty, []) loc_vars in
        let map, shared =
            List.fold_left (copy_var mk_shared_var)
                (map, []) (List.rev sk.Sk.shared) in 
        { no = 0; loc_vars = locs; shared_vars = shared;
            new_vars = locs @ shared; var_map = map }

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
            

    let assert_frame solver tt frame assertions =
        solver#comment (sprintf "frame %d" frame.no);
        let add_var v =
            solver#append_var_def v (tt#get_type v) in
        List.iter add_var frame.new_vars;
        let add_expr e =
            ignore (solver#append_expr (map_frame_vars frame frame e)) in
        List.iter add_expr assertions

end

let encode_path_elem rt tt sk start_frame pathelem =
    let each_rule frame rule =
        let new_frame = frame in (* TODO *)
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
    F.assert_frame rt#solver ntt initf sk.Sk.inits;
    let lastf = List.fold_left (encode_path_elem rt tt sk) initf path in
    rt#solver#pop_ctx;
    false

