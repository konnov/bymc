open Lexing;;
open Printf;;

open Spinlex;;
open Spin;;
open SpinTypes;;
open SpinIr;;
open SpinIrImp;;
open Debug;;

open Cfg;;

let debug = false;;

let prev_tok = ref EOF;; (* we have to remember the previous token *)

(* XXX: why is aux_bufs a reference? *)
(* lexer function decorated by a preprocessor *)
let rec lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf =
    let tok = match !aux_bufs with
      | [] -> lex_fun lexbuf  (* read from the main buffer *)

      | b :: tl -> (* read from the auxillary buffer *)
        let t = lex_fun b in
        if t != EOF then t
        else begin
            aux_bufs := tl;
            lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf
        end
    in
    let new_tok = match tok with
    (* TODO: handle macros with arguments like foo(x, y) *)
    | DEFINE(name, text) ->
        Hashtbl.add macro_tbl name text;
        lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf

    | NAME id ->
        if Hashtbl.mem macro_tbl id
        then (* substitute the contents and scan over it *)
            let newbuf = Lexing.from_string (Hashtbl.find macro_tbl id) in
            let bname = sprintf "%s:%d,%d" lexbuf.lex_curr_p.pos_fname
                lexbuf.lex_curr_p.pos_lnum
                (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol) in
            newbuf.lex_curr_p <- { newbuf.lex_curr_p with pos_fname = bname};
            aux_bufs := newbuf :: !aux_bufs;
            (* TODO: fail decently on co-recursive macro definitions *)
            lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf
        else tok

    | INCLUDE filename -> (* scan another file *)
        let path = (Filename.concat dirname filename) in
        let newbuf = Lexing.from_channel (open_in path) in
        newbuf.lex_curr_p <- { newbuf.lex_curr_p with pos_fname = filename };
        aux_bufs := newbuf :: !aux_bufs;
        lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf

      (* TODO: if/endif + ifdef/endif + if-else-endif*)
    | MACRO_IF | MACRO_IFDEF | MACRO_ELSE | MACRO_ENDIF ->
        raise (Failure (sprintf "%s is not supported" (token_s tok)))

    | MACRO_OTHER name ->
        raise (Failure (sprintf "#%s is not supported" name))

    | SND ->
        (* x!y means "send a message", but !x means "not x". They have
        different associativity and priorities. Thus, they must be different.
        *)
        if is_name !prev_tok then SND else NEG

    | _ -> tok
    in
    prev_tok := new_tok;
    new_tok
;;

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
    | _ as u -> u
;;

let parse_promela filename basename dirname =
    let lexbuf = Lexing.from_channel (open_in filename) in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = basename };
    let lfun = lex_pp dirname (Hashtbl.create 10) (ref []) Spinlex.token in
    let units, type_tab = Spin.program lfun lexbuf in

    (* postprocess: check late variable bindings and remove artifacts *)
    let units = List.map (postprocess units) units in
    if debug then begin
        (* DEBUGGING lex *)
        let t = ref EQ in
        while !t != EOF do
            t := lfun lexbuf;
            printf "%s\n" (token_s !t)
        done;

        printf "#units: %d\n" (List.length units);
        if may_log DEBUG
        then begin
            let p u = printf "%s\n" (prog_unit_s u) in
            List.iter p units;
        end
    end;
    (Program.set_type_tab type_tab (Program.program_of_units units))

