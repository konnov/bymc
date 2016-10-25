open Batteries
open Accums

open SymbSkel
open TaIr

let find_var var_map name =
    try StrMap.find name var_map
    with Not_found ->
        raise (Failure (Printf.sprintf "Variable %s not found" name))


let map_arith_expr var_fun e =
    let rec map = function
    | Int i ->
        SpinIr.IntConst i

    | Var n ->
        SpinIr.Var (var_fun n)

    | NextVar n ->
        SpinIr.UnEx (Spin.NEXT, SpinIr.Var (var_fun n))

    | Add (l, r) ->
        SpinIr.BinEx(Spin.PLUS, map l, map r)

    | Sub (l, r) ->
        SpinIr.BinEx(Spin.MINUS, map l, map r)

    | Mul (l, r) ->
        SpinIr.BinEx(Spin.MULT, map l, map r)
    in
    map e


let map_rel_expr var_fun e =
    let map tok l r =
        SpinIr.BinEx(tok,
            map_arith_expr var_fun l,
            map_arith_expr var_fun r)
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


let map_bool_expr var_fun e =
    let rec map = function
    | Cmp e ->
            map_rel_expr var_fun e

    | Not e ->
            SpinIr.UnEx (Spin.NEG, map e)

    | And (l, r) ->
            SpinIr.BinEx (Spin.AND, map l, map r)

    | Or (l, r) ->
            SpinIr.BinEx (Spin.OR, map l, map r)
    in
    map e


let map_action var_fun (lhs, exp) =
    SpinIr.BinEx (Spin.EQ,
        SpinIr.UnEx (Spin.NEXT, SpinIr.Var (var_fun lhs)),
        map_arith_expr var_fun exp)


let map_ltl_expr var_fun e =
    let rec map = function
        | LtlCmp e ->
            map_rel_expr var_fun e

        | LtlNot e ->
            SpinIr.UnEx (Spin.NEG, map e)

        | LtlF e ->
            SpinIr.UnEx (Spin.EVENTUALLY, map e)

        | LtlG e ->
            SpinIr.UnEx (Spin.ALWAYS, map e)

        | LtlAnd (l, r) ->
            SpinIr.BinEx (Spin.AND, map l, map r)

        | LtlOr (l, r) ->
            SpinIr.BinEx (Spin.OR, map l, map r)

        | LtlImplies (l, r) ->
            SpinIr.BinEx (Spin.IMPLIES, map l, map r)
    in
    map e


let map_rule var_fun r = {
    Sk.src = r.Ta.src_loc;
    Sk.dst = r.Ta.dst_loc;
    Sk.guard = map_bool_expr var_fun r.Ta.guard;
    Sk.act = List.map (map_action var_fun) r.Ta.actions
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
    let is_unknown = function
        | Unknown _ -> true
        | _ -> false
    in
    let name = function
        | Local n -> n
        | Shared n -> n
        | Param n -> n
        | Unknown n -> n
    in
    (* create one variable per location counter *)
    let loc_vars =
        let mk_loc_var map i name =
            IntMap.add i (SpinIr.new_var name) map
        in
        let n = List.length ta.Ta.locs in
        List.fold_left2 mk_loc_var IntMap.empty
            (range 0 n) (List.map fst ta.Ta.locs)
    in
    (* and map the parameters, local and global variables
       to Spin variables *)
    let var_map =
        let add m v =
            let nm = name v in
            StrMap.add nm (SpinIr.new_var nm) m
        in
        List.fold_left add StrMap.empty ta.Ta.decls
    in
    (* ...as well as location counters *)
    let var_map =
        let add_var m v = StrMap.add v#get_name v m in
        BatEnum.fold add_var var_map (IntMap.values loc_vars)
    in
    let var_fun = find_var var_map in
    let map f =
        List.filter f ta.Ta.decls
            |> List.map (fun n -> var_fun (name n)) 
    in
    let map_expr =
        SpinIr.map_vars (fun v -> SpinIr.Var (var_fun v#get_name))
    in
    let locals = map is_local in
    {
        Sk.name = ta.Ta.name; Sk.nlocs = List.length ta.Ta.locs;
        Sk.locs = List.map snd ta.Ta.locs;
        Sk.locals = map is_local;
        Sk.shared = map is_shared;
        Sk.params = map is_param;
        Sk.unknowns = map is_unknown;
        Sk.assumes = List.map (map_rel_expr var_fun) ta.Ta.assumptions;
        Sk.inits = List.map (map_rel_expr var_fun) ta.Ta.inits;
        Sk.loc_vars = loc_vars;
        Sk.nrules = List.length ta.Ta.rules;
        Sk.rules = List.map (map_rule var_fun) ta.Ta.rules;
        Sk.forms = StrMap.map (map_ltl_expr var_fun) ta.Ta.specs;
    }

