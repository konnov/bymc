(**
 
 An improvement of SlpsChecker that generates schemas on-the-fly and supports LTL(F,G).

 Igor Konnov, 2016
 *)

open Batteries
open BatPrintf

open Accums
open PorBounds
open SymbSkel
open Poset

let get_unlocked_rules sk deps uset lset =
    let unlocked_rule_nos =
        (range 0 sk.Sk.nrules)
            |> List.filter (PorBounds.is_rule_unlocked deps uset lset)
            |> PorBounds.pack_rule_set
            
    in
    PorBounds.unpack_rule_set unlocked_rule_nos deps.D.full_segment


let check_one_order sk bad_form deps tac id_order =
    let check_steady_schema uset lset =
        (* push all the unlocked rules *)
        (get_unlocked_rules sk deps uset lset) |> List.iter (tac#push_rule deps sk);
        (* TODO: in case of error, return a counterexample *)
        tac#check_property bad_form (fun _ -> ())
    in
    let rec search uset lset = function
        | [] ->
            false (* no errors: we have already checked the prefix *)

        | id :: tl -> (* activate the context, check a schema and go further *)
            let node_type = (if tl = [] then SchemaSmt.Leaf else SchemaSmt.Intermediate) in
            let is_unlocking = PSet.mem id deps.D.umask in
            let cond_expr = PSetEltMap.find id deps.D.cond_map in
            tac#enter_context;
            (* fire a sequence of rule that should unlock the condition associated with id *)
            (get_unlocked_rules sk deps uset lset) |> List.iter (tac#push_rule deps sk) ;
            (* assert that the condition is now unlocked (resp. locked) *)
            tac#assert_top [cond_expr];

            (* try to find an execution
                that does not enable new conditions and reaches a bad state *)
            let new_uset, new_lset =
                if is_unlocking
                then (PSet.add id uset), lset
                else uset, (PSet.add id lset)
            in
            tac#enter_node node_type;
            let err_found =
                if check_steady_schema new_uset new_lset
                then true (* found a bug *)
                else search new_uset new_lset tl
            in
            tac#leave_node node_type;
            tac#leave_context;
            err_found
    in
    (* check the empty context first *)
    let first_type =
        (if id_order = [] then SchemaSmt.Leaf else SchemaSmt.Intermediate) in
    tac#enter_context;
    tac#enter_node first_type;
    let err_found =
        if check_steady_schema PSet.empty PSet.empty
        (* found a bug immediately *)
        then true
        (* explore the whole tree recursively *)
        else search PSet.empty PSet.empty id_order
    in
    tac#leave_node first_type;
    tac#leave_context;
    err_found


(**
  Construct the schema tree and check it on-the-fly.

  The construction is similar to compute_static_schema_tree, but is dynamic.
 *)
let check_schema_tree_on_the_fly sk bad_form deps tac =
    let uconds = deps.D.uconds and lconds = deps.D.lconds in
    let all_ids = List.map (fun (_, id, _, _) -> id) (uconds @ lconds) in
    (* rename the condition ids to the range 0 .. nconds - 1 *)
    let assign_num (n, map) id = (n + 1, PSetEltMap.add id n map) in
    let n, enum_map = List.fold_left assign_num (0, PSetEltMap.empty) all_ids in
    let get_num id = PSetEltMap.find id enum_map in
    let rev_map =
        PSetEltMap.fold (fun k v m -> IntMap.add v k m) enum_map IntMap.empty in
    let get_id num = IntMap.find num rev_map in
    (* construct the partial order *)
    let add_orders a_id implications lst =
        (* b should come before a, as a implies b *)
        List.fold_left
            (fun orders b_id ->
                if not (PSet.elem_eq a_id b_id) && PSet.mem b_id implications
                then (get_num b_id, get_num a_id) :: orders
                else orders)
            [] all_ids
    in
    let prec_order = PSetEltMap.fold add_orders deps.D.cond_imp [] in
    (* enumerate all the linear extensions *)
    let found_bug = ref false in
    let iter = linord_iter_first n prec_order in
    while not (linord_iter_is_end iter) && not !found_bug do
        let order = BatArray.to_list (linord_iter_get iter) in
        let id_order = List.map get_id order in
        printf "  Exploring [%s]\n" (str_join "," (List.map PSet.elem_str id_order));
        if check_one_order sk bad_form deps tac id_order
        then begin
            (* found a bug *)
            printf "Found a bug! Stay tuned...\n";
            found_bug := true;
        end
        else linord_iter_next iter;
    done;
    !found_bug


