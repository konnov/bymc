open SpinIr

module StringMap = Map.Make (String)

type program = {
    f_params: var list; f_shared: var list; f_assumes: Spin.token expr list;
    f_procs: Spin.token proc list;
    f_atomics: Spin.token atomic_expr StringMap.t;
    f_ltl_forms: Spin.token expr StringMap.t
}

let empty_program = {
    f_params = []; f_shared = []; f_assumes = []; f_procs = [];
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

exception Program_error of string

let program_of_units units =
    let fold_u prog = function
    | Stmt (MDecl(_, v, _)) ->
            if v#is_symbolic
            then { prog with f_params = (v :: prog.f_params) }
            else { prog with f_shared = (v :: prog.f_shared) }
    | Stmt (MDeclProp(_, v, e)) ->
            let new_ap = (StringMap.add v#get_name e prog.f_atomics) in
            { prog with f_atomics = new_ap }
    | Stmt (MExpr(_, e)) ->
            { prog with f_assumes = (e :: prog.f_assumes) }
    | Stmt (_ as s) ->
            raise (Program_error
                ("Unexpected top-level statement: " ^ (SpinIrImp.mir_stmt_s s)))
    | Proc p ->
            { prog with f_procs = p :: prog.f_procs }
    | Ltl (name, ltl_form) ->
            let new_fs = (StringMap.add name ltl_form prog.f_ltl_forms) in
            { prog with f_ltl_forms = new_fs }
    | None ->
            prog
    in
    List.fold_left fold_u empty_program (List.rev units)


let units_of_program program =
    let var_to_decl v =
        Stmt (MDecl (-1, v, (Nop ""))) in
    let atomic_to_decl name expr accum =
        (Stmt (MDeclProp(-1, new var(name), expr))) :: accum in
    let form_to_ltl name expr accum =
        (Ltl(name, expr)) :: accum in
    let to_expr e = Stmt (MExpr(-1, e)) in
    let to_proc p = Proc p in
    (List.concat
        [(List.map var_to_decl program.f_params);
         (List.map var_to_decl program.f_shared);
         (StringMap.fold atomic_to_decl program.f_atomics []);
         (List.map to_expr program.f_assumes);
         (List.map to_proc program.f_procs);
         (StringMap.fold form_to_ltl program.f_ltl_forms [])])

