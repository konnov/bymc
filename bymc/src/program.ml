open Accums
open SpinIr

type expr_t = Spin.token expr

type path_elem_t =
    | State of expr_t list (* a state as a set of variable constraints *)
    | Intrinsic of string StringMap.t (* intrinsic data: key=value *)

type path_t = path_elem_t list
type lasso_t = path_t * path_t (* (prefix, cycle) *)

exception Program_error of string

type program_t = {
    f_uid: int; (* unique identifier of every program *)
    f_params: var list; f_instrumental: var list;
    f_shared: (var * expr_t) list; 
    f_sym_tab: symb_tab; (* kept internally *)
    f_type_tab: data_type_tab;
    f_assumes: expr_t list; f_unsafes: string list;
    f_procs: Spin.token proc list;
    f_atomics: (var * Spin.token atomic_expr) list;
    f_ltl_forms: expr_t StringMap.t
}

let empty = {
    f_uid = 0;
    f_params = []; f_shared = []; f_instrumental = [];
    f_sym_tab = new symb_tab ""; (* global scope *)
    f_type_tab = new data_type_tab;
    f_assumes = []; f_procs = []; f_unsafes = [];
    f_atomics = []; f_ltl_forms = StringMap.empty
}

let prog_uid prog =
    prog.f_uid


let update_sym_tab prog =
    let var_to_symb v = (v :> symb) in
    let proc_to_symb p = (p :> symb) in (* can we reuse var_to_symb? *)
    let string_to_symb s = new symb(s) in
    let map_to_symb m =
        (* backport to 3.10.2 *)
        StringMap.fold (fun k _ a -> (string_to_symb k) :: a) m []
        (* the new code:
        List.map (fun (k, _) -> string_to_symb k) (StringMap.bindings m) *)
    in
    let take1 lst = List.map (fun (a1, _) -> a1) lst in
    let syms =
        (List.map var_to_symb prog.f_params)
        @ (List.map var_to_symb (take1 prog.f_shared))
        @ (List.map var_to_symb prog.f_instrumental)
        @ (List.map proc_to_symb prog.f_procs)
        @ (List.map var_to_symb (take1 prog.f_atomics))
        @ (map_to_symb prog.f_ltl_forms)
    in
    prog.f_sym_tab#set_syms syms;
    (* XXX: processes are not copied but their attributes are updated! *)
    let update_proc_tab p = p#set_parent prog.f_sym_tab in
    List.iter update_proc_tab prog.f_procs;
    prog

let get_params prog =
    prog.f_params

let set_params new_params prog =
    update_sym_tab { prog with f_uid = fresh_id (); f_params = new_params }

let get_shared_with_init prog =
    prog.f_shared

let set_shared_with_init new_shared_pairs prog =
    update_sym_tab {
        prog with f_uid = fresh_id (); f_shared = new_shared_pairs
    }

let get_shared prog =
    List.map (fun (v, _) -> v) prog.f_shared

let set_shared new_shared prog =
    update_sym_tab {
        prog with f_uid = fresh_id ();
            f_shared = (List.map (fun v -> (v, Nop "")) new_shared)
    }

let get_instrumental prog =
    prog.f_instrumental

let set_instrumental new_instr prog =
    update_sym_tab { prog with f_uid = fresh_id (); f_instrumental = new_instr }

let get_type prog variable =
    try prog.f_type_tab#get_type variable
    with Not_found ->
        raise (Program_error ("No data type for variable " ^ variable#get_name))

let set_type_tab type_tab prog =
    { prog with f_uid = fresh_id(); f_type_tab = type_tab }

let get_type_tab prog =
    prog.f_type_tab

(* no set_sym_tab: it is updated automatically *)
let get_sym_tab prog =
    prog.f_sym_tab

let get_assumes prog = prog.f_assumes
let set_assumes new_assumes prog =
    {prog with f_uid = fresh_id (); f_assumes = new_assumes}

let get_unsafes prog = prog.f_unsafes
let set_unsafes new_unsafes prog =
    {prog with f_uid = fresh_id (); f_unsafes = new_unsafes}

let get_procs prog = prog.f_procs

let set_procs new_procs prog =
    update_sym_tab { prog with f_uid = fresh_id (); f_procs = new_procs }

let get_atomics prog = prog.f_atomics

let get_atomics_map prog =
    let add m (v, e) = StringMap.add v#get_name e m in
    List.fold_left add StringMap.empty prog.f_atomics

let set_atomics new_atomics prog =
    update_sym_tab { prog with f_uid = fresh_id (); f_atomics = new_atomics }

let get_ltl_forms prog =
    prog.f_ltl_forms

let set_ltl_forms new_ltl_forms prog =
    update_sym_tab {
        prog with f_uid = fresh_id (); f_ltl_forms = new_ltl_forms
    }

let get_ltl_forms_as_hash prog =
    let h = Hashtbl.create 10 in
    let to_hash name form = Hashtbl.add h name form in
    let _ = StringMap.mapi to_hash prog.f_ltl_forms in
    h

let is_global prog v =
    try v = List.find ((=) v) (prog.f_params @ (get_shared prog))
    with Not_found -> false

let is_not_global prog v =
    not (is_global prog v)

let get_all_locals prog =
    let collect lst = function
    | MDecl (_, v, _) -> v :: lst
    | _ -> lst
    in
    let collect_proc lst p =
        List.fold_left collect lst p#get_stmts
    in
    List.fold_left collect_proc [] prog.f_procs


let program_of_units type_tab units =
    let fold_u prog = function
    | Stmt (MDecl(_, v, e)) ->
            if v#is_symbolic
            then { prog with f_params = (v :: prog.f_params) }
            else if v#is_instrumental
            then { prog with f_instrumental = (v :: prog.f_instrumental) }
            else { prog with f_shared = ((v, e) :: prog.f_shared) }
    | Stmt (MDeclProp(_, v, e)) ->
            { prog with f_atomics = (v, e) :: prog.f_atomics }
    | Stmt (MAssume(_, e)) ->
            { prog with f_assumes = (e :: prog.f_assumes) }
    | Stmt (MUnsafe(_, s)) ->
            { prog with f_unsafes = (s :: prog.f_unsafes) }
    | Stmt (_ as s) ->
            raise (Program_error
                ("Unexpected top-level statement: " ^ (SpinIrImp.mir_stmt_s s)))
    | Proc p ->
            { prog with f_procs = p :: prog.f_procs }
    | Ltl (name, ltl_form) ->
            let new_fs = (StringMap.add name ltl_form prog.f_ltl_forms) in
            { prog with f_ltl_forms = new_fs }
    | EmptyUnit ->
            prog
    in
    let prog = List.fold_left fold_u empty (List.rev units) in
    update_sym_tab { prog with f_uid = fresh_id (); f_type_tab = type_tab }


let units_of_program program =
    let var_to_decl v =
        Stmt (MDecl (fresh_id (), v, (Nop ""))) in
    let var_init_to_decl (v, e) =
        Stmt (MDecl (fresh_id (), v, e)) in
    let atomic_to_decl (v, e) =
        Stmt (MDeclProp(fresh_id (), v, e)) in
    let form_to_ltl name expr accum =
        (Ltl(name, expr)) :: accum in
    let to_assume e = Stmt (MAssume(fresh_id (), e)) in
    let to_unsafe e = Stmt (MUnsafe(fresh_id (), e)) in
    let to_proc p = Proc p in
    (List.concat
        [(List.map var_to_decl program.f_params);
         (List.map var_init_to_decl program.f_shared);
         (List.map var_to_decl program.f_instrumental);
         (List.map atomic_to_decl program.f_atomics);
         (List.map to_assume program.f_assumes);
         (List.map to_unsafe program.f_unsafes);
         (List.map to_proc program.f_procs);
         (StringMap.fold form_to_ltl program.f_ltl_forms [])])

