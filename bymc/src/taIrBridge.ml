open Batteries
open Accums

open SymbSkel
open TaIr

let map_arith_expr var_map e =
    let rec map = function
    | Int i ->
        SpinIr.IntConst i

    | Var n ->
        SpinIr.Var (StrMap.find n var_map)

    | NextVar n ->
        SpinIr.UnEx (Spin.NEXT, SpinIr.Var (StrMap.find n var_map))

    | Add (l, r) ->
        SpinIr.BinEx(Spin.PLUS, map l, map r)

    | Sub (l, r) ->
        SpinIr.BinEx(Spin.MINUS, map l, map r)

    | Mul (l, r) ->
        SpinIr.BinEx(Spin.MULT, map l, map r)
    in
    map e


let map_rel_expr var_map e =
    let map tok l r =
        SpinIr.BinEx(tok,
            map_arith_expr var_map l,
            map_arith_expr var_map r)
    in
    match e with
    | Eq (l, r) ->
            map Spin.EQ l r

    | Neq (l, r) -> 
            map Spin.NE l r

    | Lt (l, r) ->
            map Spin.LT l r

    | Leq (l, r) ->
            map Spin.LE l r

    | Gt (l, r) ->
            map Spin.GT l r

    | Geq (l, r) ->
            map Spin.GE l r


let map_bool_expr var_map e =
    let rec map = function
    | Cmp e ->
            map_rel_expr var_map e

    | Not e ->
            SpinIr.UnEx (Spin.NEG, map e)

    | And (l, r) ->
            SpinIr.BinEx (Spin.AND, map l, map r)

    | Or (l, r) ->
            SpinIr.BinEx (Spin.OR, map l, map r)
    in
    map e


let map_rule var_map r = {
    Sk.src = r.Ta.src_loc;
    Sk.dst = r.Ta.dst_loc;
    Sk.guard = map_bool_expr var_map r.Ta.guard;
    Sk.act = [ map_bool_expr var_map r.Ta.action ]
}


let skel_of_ta ta =
    let is_local = function
        | Local _ -> true
        | _ -> false
    in
    let is_shared = function
        | Shared _ -> true
        | _ -> false
    in 
    let is_param = function
        | Param _ -> true
        | _ -> false
    in
    let name = function
        | Local n -> n
        | Shared n -> n
        | Param n -> n
    in
    let var_map =
        let add m v =
            let nm = name v in
            StrMap.add nm (SpinIr.new_var nm) m
        in
        List.fold_left add StrMap.empty ta.Ta.decls
    in
    let map f =
        List.filter f ta.Ta.decls
            |> List.map (fun n -> StrMap.find (name n) var_map) 
    in
    let map_expr =
        SpinIr.map_vars (fun v -> SpinIr.Var (StrMap.find v#get_name var_map))
    in
    let locals = map is_local in
    let loc_vars =
        List.fold_left2
            (fun m i v -> IntMap.add i v m)
            IntMap.empty (range 0 (List.length locals)) locals
    in
    {
        Sk.name = ta.Ta.name; Sk.nlocs = List.length ta.Ta.locs;
        Sk.locs = List.map snd ta.Ta.locs;
        Sk.locals = map is_local;
        Sk.shared = map is_shared;
        Sk.params = map is_param;
        Sk.assumes = List.map (map_rel_expr var_map) ta.Ta.assumptions;
        Sk.inits = List.map (map_rel_expr var_map) ta.Ta.inits;
        Sk.loc_vars = loc_vars;
        Sk.nrules = List.length ta.Ta.rules;
        Sk.rules = List.map (map_rule var_map) ta.Ta.rules;
        Sk.forms = StrMap.empty; (* TODO: add the formulas *)
    }

