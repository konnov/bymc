(**
  Synthesizing threshold automata using CEGYS.

  @author Igor Konnov, 2016
 *)

open Printf

open Accums
open Spin
open SpinIr
open SymbSkel


let map_of_unknowns_vec (vec: (string * Spin.token SpinIr.expr) list) =
    let add map (name, exp) = StrMap.add name exp map in
    List.fold_left add StrMap.empty vec


(** compute the initial vector of unknowns *)
let init_unknowns_vec sk =
    let mk_pair v = (v#get_name, IntConst 0) in
    List.map mk_pair sk.Sk.unknowns


(* compute the next vector of unknowns *)
let next_unknowns_vec sk vec =
    vec

let unknowns_vec_s vec =
    let pair_s (n, e) =
        sprintf "%s = %s" n (SpinIrImp.expr_s e)
    in
    str_join ", " (List.map pair_s vec)


(** replace unknowns with the values given in the unknowns vector *)
let replace_unknowns sk unknowns_vec =
    let vec_map = map_of_unknowns_vec unknowns_vec in
    let sub exp =
        let map_fun v =
            try StrMap.find v#get_name vec_map
            with Not_found -> Var v
        in
        Simplif.compute_consts (map_vars map_fun exp)
    in
    let map_rule r =
        { r with Sk.guard = sub r.Sk.guard;
                 Sk.act = List.map sub r.Sk.act }
    in
    { sk with Sk.unknowns = [];
              Sk.assumes = List.map sub sk.Sk.assumes;
              Sk.rules = List.map map_rule sk.Sk.rules;
              Sk.inits = List.map sub sk.Sk.inits }


