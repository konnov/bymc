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
        accel_v: var; (* acceleration factor of the transition leading to the frame *)
        loc_vars: var list; (* one copy per location *)
        shared_vars: var list; (* one copy per shared variable *)
        new_vars: var list;
            (*  the variables (from loc_vars and shared_vars)
                introduced in this frame  *)
        var_map: var IntMap.t;
            (* mapping id of the original variable to its copy in the frame *)
    }

    let mk_loc_var (tt: data_type_tab) frame_no proto =
        let nv = proto#fresh_copy (sprintf "F%d_at_%s" frame_no proto#get_name) in
        tt#set_type nv (tt#get_type proto);
        nv


    let mk_shared_var (tt: data_type_tab) frame_no proto =
        let nv = proto#fresh_copy (sprintf "F%d_g_%s" frame_no proto#get_name) in
        tt#set_type nv (tt#get_type proto);
        nv

        (* TODO: myself 2015, please write a comment! *)
    let advance_frame tt sk prev_frame is_var_updated_fun =
        let next_no = 1 + prev_frame.no in 
        let copy_var ctor_fun (map, vs, new_vs) basev v =
            if is_var_updated_fun basev v
            then let nv = ctor_fun tt next_no basev in
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
        let accel_v = new_var (sprintf "F%d_warp" next_no) in
        tt#set_type accel_v (new data_type SpinTypes.TUNSIGNED);
        { no = next_no; accel_v = accel_v;
            loc_vars = locs; shared_vars = shared;
            new_vars = new_vars; var_map = map }

    let init_frame tt sk =
        let loc_vars = List.map (Sk.locvar sk) (range 0 sk.Sk.nlocs) in
        let empty_frame = {
            no = -1; accel_v = new_var "";
            loc_vars = loc_vars; shared_vars = sk.Sk.shared;
            new_vars = []; var_map = IntMap.empty
        }
        in
        advance_frame tt sk empty_frame (fun _ _ -> true)

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
        add_var frame.accel_v;
        List.iter add_var frame.new_vars

    let assert_frame solver tt frame next_frame assertions =
        let add_expr e =
            ignore (solver#append_expr (map_frame_vars frame next_frame e)) in
        List.iter add_expr assertions

end

let collect_next_vars e =
    let rec f set = function
        | UnEx (Spin.NEXT, Var v) -> IntSet.add v#id set
        | UnEx (_, e) -> f set e
        | BinEx (_, l, r) -> f (f set l) r
        | _ -> set
    in
    f IntSet.empty e


let encode_path_elem rt tt sk start_frame pathelem =
    let each_rule is_milestone (frame, fs) rule_no =
        let rule = List.nth sk.Sk.rules rule_no in
        let src_loc_v = List.nth frame.F.loc_vars rule.Sk.src in
        let dst_loc_v = List.nth frame.F.loc_vars rule.Sk.dst in
        let next_shared =
            List.fold_left IntSet.union IntSet.empty
                (List.map collect_next_vars rule.Sk.act) in
        let is_new_f basev v =
            v#id = src_loc_v#id || v#id = dst_loc_v#id
                || IntSet.mem basev#id next_shared
        in
        let new_frame = F.advance_frame tt sk frame is_new_f in
        F.declare_frame rt#solver tt new_frame;
        let move loc_var sign =
            (* k'[loc] = k[loc] +/- accel *)
            BinEx (Spin.EQ, UnEx (Spin.NEXT, Var loc_var),
                BinEx (sign, Var loc_var, Var new_frame.F.accel_v))
        in
        F.assert_frame rt#solver tt frame new_frame [move src_loc_v Spin.MINUS];
        F.assert_frame rt#solver tt frame new_frame [move dst_loc_v Spin.PLUS];
        if is_milestone
        then F.assert_frame rt#solver tt frame new_frame [rule.Sk.guard];

        (* accelerate actions! *)
        F.assert_frame rt#solver tt frame new_frame rule.Sk.act;
        (new_frame, new_frame :: fs)
    in
    let rec sum = function
        | [] -> Const 0
        | [frame] -> Var frame.F.accel_v
        | frame :: tl -> BinEx (Spin.PLUS, Var frame.F.accel_v, sum tl)
    in
    let each_path_elem = function
    | MaybeMile (_, rules) ->
            let endf, new_frames =
                List.fold_left (each_rule true) (start_frame, []) rules in
            let constr = BinEx (Spin.EQ, Const 1, sum new_frames) in
            ignore (rt#solver#append_expr constr);
            endf

    | Seg rules ->
            let endf, _ =
                List.fold_left (each_rule false) (start_frame, []) rules in
            endf
    in
    each_path_elem pathelem


let is_error_path rt tt sk path =
    rt#solver#push_ctx;
    let ntt = tt#copy in
    let initf = F.init_frame ntt sk in
    F.declare_frame rt#solver ntt initf;
    F.assert_frame rt#solver ntt initf initf sk.Sk.inits;
    let lastf = List.fold_left (encode_path_elem rt tt sk) initf path in
    let is_sat = rt#solver#check in
    rt#solver#pop_ctx;
    is_sat

