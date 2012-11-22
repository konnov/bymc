module StringMap = Map.Make (String)

type program = {
    f_params: var list; f_shared: var_list; f_assumes: Spin.token expr list;
    f_procs: Spin.token proc StringMap; f_atomics: Spin.token expr StringMap;
    f_ltl_forms: Spin.token expr StringMap
}

let empty_program = {
    f_params = []; f_shared = []; f_assumes = []; f_procs = StringMap.empty;
    f_atomics = StringMap.empty; f_ltl_forms = StringMap.empty
}

let get_params prog = prog.f_params
let set_params prog new_params = {prog with f_params = new_params}

let get_shared prog = prog.f_shared
let set_shared prog new_shared = {prog with f_shared = new_shared}

let get_assumes prog = prog.f_assumes
let set_assumes prog new_assumes = {prog with f_assumes = new_assumes}

let get_procs prog = prog.f_procs
let set_procs prog new_procs = {prog with f_procs = new_procs}

let get_atomics prog = prog.f_atomics
let set_atomics prog new_atomics = {prog with f_atomics = new_atomics}

let get_ltl_forms prog = prog.f_ltl_forms
let set_ltl_forms prog new_ltl_forms = {prog with f_ltl_forms = new_ltl_forms}

let program_of_units units =
    let fold_u prog = function
    | Stmt (MDecl(_, v, _)) ->
            if v#is_symbolic
            then { prog with f_params = (v :: prog.f_params) }
            else { prog with f_params = (v :: prog.f_shared) }
    | Stmt (MDeclProp(_, v, e)) ->
            let new_ap = (StringMap.add v#get_name e prog.f_atomics) in
            { prog with f_atomics = new_ap }
    | Stmt s ->
            { prog with f_assumes = (s :: prog.f_assumes) }
    | Proc p ->
            { prog with f_proc = p :: prog.f_procs }
    | Ltl (name, ltl_form) ->
            let new_fs = (StringMap.add name ltl_form prog.f_ltl_forms) in
            { prog with f_ltl_forms = new_fs }
    in
    List.fold_left fold_u empty_program (List.rev units)

