(*
The internal state of the spin parser -- use with care and as little as possible.
As ocamlyacc exports nothing but the start non-terminals, we keep the global
state in this module. See spinParserCtx.mli
 *)

open SpinIr

exception Not_implemented of string
exception Parse_error of string
exception State_error of string

type spin_parser_state_t = {
    err_cnt: int; global_scope: symb_tab; spec_scope: symb_tab;
    scope_stack: symb_tab list; type_tab: data_type_tab
}

let current_parser_state = ref None

let get_state _ =
    match !current_parser_state with
    | Some s -> s
    | None -> raise (State_error "get_state is called before reset_state")

let reset_state _ =
    let global = new symb_tab "" in
    let s = {
        err_cnt = 0; global_scope = global; spec_scope = new symb_tab "spec";
        scope_stack = [global]; type_tab = new data_type_tab
    } in
    current_parser_state := Some s


let err_cnt _ =
    (get_state ()).err_cnt

let inc_err_cnt _ =
    let s = get_state () in
    current_parser_state := Some { s with err_cnt = s.err_cnt + 1 }

let global_scope _ = (get_state ()).global_scope
let spec_scope _ = (get_state ()).spec_scope

let top_scope _ = List.hd ((get_state ())).scope_stack

let push_scope scope =
    let s = get_state () in
    scope#set_parent (List.hd s.scope_stack);
    current_parser_state := Some { s with scope_stack = scope :: s.scope_stack }

let pop_scope _ =
    let s = get_state () in
    if (List.length s.scope_stack) > 1
    then current_parser_state :=
        Some { s with scope_stack = List.tl s.scope_stack }
    else raise (State_error "Trying to pop the global scope")

let type_tab _ = (get_state ()).type_tab

