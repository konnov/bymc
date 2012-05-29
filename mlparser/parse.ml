open Lexing;;
open Printf;;

open Spinlex;;
open Spin;;
open Spin_types;;
open Spin_ir;;
open Spin_ir_imp;;

open Cfg;;

let debug = false;;

(* lexer function decorated by a preprocessor *)
let rec lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf =
    let tok = match !aux_bufs with
      [] -> lex_fun lexbuf  (* read from the main buffer *)

      | b :: tl -> (* read from the auxillary buffer *)
        let t = lex_fun b in
        if t != EOF then t
        else begin
            aux_bufs := tl;
            lex_pp dirname macro_tbl aux_bufs lex_fun lexbuf
        end
    in
    match tok with
      (* TODO: handle macros with arguments foo(x, y) *)
      DEFINE(name, text) ->
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

      | _ -> tok
;;


let parse_promela filename basename dirname =
    let lexbuf = Lexing.from_channel (open_in filename) in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = basename };
    let lfun = lex_pp dirname (Hashtbl.create 10) (ref []) Spinlex.token in
    let units = Spin.program lfun lexbuf in

    (* postprocess: remove artifacts that complicate further processing *)
    let units = List.map
        (function
            | Proc p ->
                Proc (proc_replace_body p (merge_neighb_labels p#get_stmts))
            | _ as u -> u )
        units
    in
    if debug then begin
        (* (* DEBUGGING lex *)
        let t = ref EQ in
        while !t != EOF do
            t := lfun lexbuf;
            printf "%s\n" (token_s !t)
        done
        *)

        printf "#units: %d\n" (List.length units);
        let p u = printf "%s\n" (prog_unit_s u) in
        List.iter p units;

        List.iter
            (function
                | Proc p ->
                    let bbs = mk_cfg p#get_stmts in
                    Hashtbl.iter (fun _ bb -> printf "%s\n" bb#str) bbs
                | _ -> () )
            units;
    end;
    units

