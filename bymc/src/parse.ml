open Lexing
open Printf

open Accums
open Debug
open Spinlex
open Spin
open SpinTypes
open SpinIr
open SpinIrImp

open Cfg

let debug = false

type lex_state = {
    dirname: string; macros: (string, string) Hashtbl.t;
    prev_tok: token;
    pragmas: (string * string) list; aux_bufs: lexbuf list;
    macro_if_stack: bool list; is_enabled: bool
}

(* XXX: why is aux_bufs a reference? *)
(* lexer function decorated by a preprocessor *)
let rec lex_pp (lexst: lex_state ref) lex_fun lexbuf =
    let tok = match (!lexst).aux_bufs with
      | [] -> lex_fun lexbuf  (* read from the main buffer *)

      | b :: tl -> (* read from the auxillary buffer *)
        let t = lex_fun b in
        if t != EOF then t
        else begin
            lexst := { !lexst with aux_bufs = tl };
            lex_pp lexst lex_fun lexbuf
        end
    in
    let if_macro ls is_ifdef name = 
        let is_true = Hashtbl.mem ls.macros name in
        let is_enabled = if is_ifdef then is_true else not is_true in
        { ls with is_enabled = is_enabled;
          macro_if_stack = (is_true :: ls.macro_if_stack) }
    in
    let new_tok = match tok with
    (* TODO: handle macros with arguments like foo(x, y) *)
    | DEFINE(name, text) ->
        Hashtbl.add (!lexst).macros name text;
        lex_pp lexst lex_fun lexbuf

    | PRAGMA(name, text) ->
        lexst := { !lexst with pragmas = (name, text) :: !lexst.pragmas };
        lex_pp lexst lex_fun lexbuf

    | NAME id ->
        if Hashtbl.mem (!lexst).macros id
        then (* substitute the contents and scan over it *)
            let newbuf = Lexing.from_string (Hashtbl.find (!lexst).macros id) in
            let bname = sprintf "%s:%d,%d" lexbuf.lex_curr_p.pos_fname
                lexbuf.lex_curr_p.pos_lnum
                (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol) in
            newbuf.lex_curr_p <- { newbuf.lex_curr_p with pos_fname = bname};
            lexst := { !lexst with aux_bufs = newbuf :: !lexst.aux_bufs };
            (* TODO: fail decently on co-recursive macro definitions *)
            lex_pp lexst lex_fun lexbuf
        else tok

    | INCLUDE filename -> (* scan another file *)
        let path = Filename.concat (!lexst).dirname filename in
        let newbuf = Lexing.from_channel (open_in path) in
        newbuf.lex_curr_p <- { newbuf.lex_curr_p with pos_fname = filename };
        lexst := { !lexst with aux_bufs = newbuf :: (!lexst).aux_bufs };
        lex_pp lexst lex_fun lexbuf

    | MACRO_IFDEF name -> 
        lexst := if_macro !lexst true name;
        lex_pp lexst lex_fun lexbuf

    | MACRO_IFNDEF name -> 
        lexst := if_macro !lexst false name;
        lex_pp lexst lex_fun lexbuf

    | MACRO_ELSE ->
        lexst := {
            !lexst with is_enabled = not (!lexst).is_enabled;
            macro_if_stack =
                (not (!lexst).is_enabled) :: (List.tl (!lexst).macro_if_stack)
        };
        lex_pp lexst lex_fun lexbuf

    | MACRO_ENDIF ->
        let new_stack =
            try List.tl !lexst.macro_if_stack
            with Failure _ -> 
                let pos = sprintf "%s:%d,%d" lexbuf.lex_curr_p.pos_fname
                    lexbuf.lex_curr_p.pos_lnum
                    (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol)
                in
                raise (SpinParserState.Parse_error
                    (sprintf "%s #endif does not have matching #ifdef/ifndef" pos))
        in
        let is_enabled =
            if (List.length new_stack) > 0 then List.hd new_stack else true in
        lexst := {
            !lexst with macro_if_stack = new_stack; is_enabled = is_enabled
        };
        lex_pp lexst lex_fun lexbuf

      (* TODO: if/endif *)
    | MACRO_IF ->
        raise (Failure (sprintf "%s is not supported" (token_s tok)))

    | MACRO_OTHER name ->
        raise (Failure (sprintf "%s is not supported" name))

    | SND ->
        (* x!y means "send a message", but !x means "not x". They have
        different associativity and priorities. Thus, they must be different.
        *)
        if is_name (!lexst).prev_tok then SND else NEG

    | _ -> tok
    in
    if (!lexst).is_enabled
    then begin
        lexst := { !lexst with prev_tok = new_tok };
        new_tok
    end else
        lex_pp lexst lex_fun lexbuf


let postprocess all_units u =
    let rec bind_var = function
        | UnEx (t, e1) -> UnEx (t, bind_var e1)
        | BinEx (t, e1, e2) -> BinEx (t, bind_var e1, bind_var e2)
        | Var v ->
            let is_ref_proc = function
                | Proc p -> p#get_name = v#proc_name
                | _ -> false
            in
            if v#proc_name = ""
            then Var v
            else
            begin
                let host =
                    try 
                        List.find is_ref_proc all_units
                    with Not_found ->
                        raise (Failure
                            (sprintf "Process %s not found" v#proc_name))
                in
                try
                    let bound = (proc_of_unit host)#lookup v#get_name in
                    bound#as_var#set_proc_name v#proc_name;
                    Var bound#as_var
                with Symbol_not_found _ ->
                    raise (Failure
                        (sprintf "Process %s does not have variable %s"
                            v#proc_name v#get_name))
            end

        | _ as e -> e
    in
    (* Proc (proc_replace_body p (merge_neighb_labels p#get_stmts)) *)
    let rec on_atomic = function
        | PropAll e -> PropAll (bind_var e)
        | PropSome e -> PropSome (bind_var e)
        | PropGlob e -> PropGlob (bind_var e)
        | PropAnd (l, r) -> PropAnd (on_atomic l, on_atomic r)
        | PropOr (l, r) -> PropOr (on_atomic l, on_atomic r)
    in
    match u with
    | Stmt (MDeclProp (id, v, ae)) ->
        Stmt (MDeclProp (id, v, on_atomic ae))

    | Proc p ->
        let sub = function
        | MExpr (id, e) -> MExpr (id, bind_var e)
        | _ as s -> s
        in
        Proc (proc_replace_body p
            (List.map (sub_basic_stmt sub) p#get_stmts))

    | _ as u -> u


let init_macros opts =
    let macros = Hashtbl.create 8 in
    let tool = match opts.Options.mc_tool with
    | Options.ToolSpin -> "SPIN"
    | Options.ToolNusmv -> "NUSMV"
    in
    Hashtbl.add macros tool "1";
    let add_macro_opt full_name value =
        let pl = String.length Options.macro_prefix in
        let nl = String.length full_name in
        if nl > pl && ((String.sub full_name 0 pl) = Options.macro_prefix)
        then let name = String.sub full_name pl (nl - pl) in
            Hashtbl.replace macros name value
    in
    StrMap.iter add_macro_opt opts.Options.plugin_opts;
    macros


let parse_promela_of_chan opts chan basename dirname =
    let lexbuf = Lexing.from_channel chan in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = basename };
    let lexst = ref {
        dirname = dirname; macros = init_macros opts;
        prev_tok = EOF; pragmas = []; aux_bufs = []; macro_if_stack = [];
        is_enabled = true
    }
    in
    let ppfun = lex_pp lexst Spinlex.token in
    SpinParserState.reset_state ();
    let units, type_tab = Spin.program ppfun lexbuf in

    (* postprocess: check late variable bindings and remove artifacts *)
    let units = List.map (postprocess units) units in
    if debug then begin
        (* DEBUGGING lex *)
        let t = ref EQ in
        while !t != EOF do
            t := ppfun lexbuf;
            printf "%s\n" (token_s !t)
        done;

        printf "#units: %d\n" (List.length units);
        if may_log DEBUG
        then begin
            let p u = printf "%s\n" (prog_unit_s u) in
            List.iter p units;
        end
    end;
    Program.program_of_units type_tab units, (!lexst).pragmas


let parse_promela opts filename basename dirname =
    let chan = open_in filename in
    parse_promela_of_chan opts chan basename dirname


let parse_expr sym_tab str =
    let lexbuf = Lexing.from_string str in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "<string>" };
    SpinParserState.reset_state ();
    SpinParserState.push_scope sym_tab;
    Spin.expr Spinlex.token lexbuf

