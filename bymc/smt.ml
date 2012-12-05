(* utility functions to integrate with Yices *)

open Printf;;
open Str;;

open SpinTypes;;
open Spin;;
open SpinIr;;
open SpinIrImp;;
open Debug;;

exception Smt_error of string;;
exception Communication_failure of string;;

let rec var_to_smt var =
    let wrap_arr type_s =
        if var#is_array
        then sprintf "(-> (subrange 0 %d) %s)" (var#get_num_elems - 1) type_s
        else type_s
    in
    let ts = match var#get_type with
    | TBIT -> wrap_arr "bool"
    | TBYTE -> wrap_arr "int"
    | TSHORT -> wrap_arr "int"
    | TINT -> wrap_arr "int"
    | TUNSIGNED -> wrap_arr "nat"
    | TCHAN -> raise (Failure "Type chan is not supported")
    | TMTYPE -> raise (Failure "Type mtype is not supported")
    | TPROPOSITION -> raise (Failure "Type proposition is not supported")
    in
    sprintf "(define %s :: %s)" var#get_name ts
;;

let rec expr_to_smt e =
    match e with
    | Nop comment -> sprintf ";; %s\n" comment
    | Const i -> string_of_int i
    | Var v -> v#get_name
    | UnEx (tok, f) ->
        begin match tok with
        | UMIN -> sprintf "(- %s)" (expr_to_smt f)
        | NEG  -> sprintf "(not %s)" (expr_to_smt f)
        | _ ->
            raise (Failure
                (sprintf "No idea how to translate %s to SMT" (token_s tok)))
        end
    | BinEx (tok, l, r) ->
        begin match tok with
        | PLUS  -> sprintf "(+ %s %s)" (expr_to_smt l) (expr_to_smt r)
        | MINUS -> sprintf "(- %s %s)" (expr_to_smt l) (expr_to_smt r)
        | MULT  -> sprintf "(* %s %s)" (expr_to_smt l) (expr_to_smt r)
        | DIV   -> sprintf "(div %s %s)" (expr_to_smt l) (expr_to_smt r)
        | MOD   -> sprintf "(mod %s %s)" (expr_to_smt l) (expr_to_smt r)
        | GT    -> sprintf "(> %s %s)" (expr_to_smt l) (expr_to_smt r)
        | LT    -> sprintf "(< %s %s)" (expr_to_smt l) (expr_to_smt r)
        | GE    -> sprintf "(>= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | LE    -> sprintf "(<= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | EQ    -> sprintf "(= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | NE    -> sprintf "(/= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | AND   -> sprintf "(and %s %s)" (expr_to_smt l) (expr_to_smt r)
        | OR    -> sprintf "(or %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | ARR_ACCESS -> sprintf "(%s %s)" (expr_to_smt l) (expr_to_smt r)
        | _ -> raise (Failure
                (sprintf "No idea how to translate %s to SMT" (token_s tok)))
        end

    | Phi (lhs, rhs) ->
            raise (Failure "Phi to SMT is not supported")

    | LabelRef (proc_name, lab_name) ->
            raise (Failure "LabelRef to SMT is not supported")
;;

(*
  The wrapper of an SMT solver (yices).
  XXX: if yices dies accidentally, the parent (OCaml) dies as well.
  Do something to notify the user.
 *)
class yices_smt =
    object(self)
        (* for how long we wait for output from yices if check is issued *)
        val check_timeout_sec = 3600.0
        (* for how long we wait for output from yices if another command is issued*)
        val timeout_sec = 10.0
        val mutable pid = 0
        val mutable cin = stdin
        val mutable cout = stdout
        val mutable cerr = stdin
        val mutable clog = stdout
        val mutable cerrlog = stdout
        val mutable debug = false
        val mutable collect_asserts = false
        val mutable poll_tm_sec = 10.0

        method start =
            let pin, pout, perr =
                Unix.open_process_full "yices" (Unix.environment ()) in
            cin <- pin;
            cout <- pout;
            cerr <- perr;
            clog <- open_out "yices.log";
            cerrlog <- open_out "yices.err";
            self#append "(set-verbosity! 2)\n" (* to track assert+ *)
        
        method stop =
            close_out clog;
            close_out cerrlog;
            Unix.close_process_full (cin, cout, cerr)

        method poll poll_i poll_o =
            let read_err = ref true in
            let rs = ref [] in
            let ws = ref [] in
            let log_input_to_errlog fd = 
                let buf_len = 50 in
                let buf = String.create buf_len in
                let stop = ref false in
                while not !stop do
                    let len = Unix.read fd buf 0 buf_len in
                    printf "%s\n" buf; flush stdout;
                    fprintf cerrlog "%s" buf; flush cerrlog;
                    stop := (len < buf_len);
                done
            in
            (* read the error input first as it can block other chans *)
            while !read_err do
                let ins, outs, errs =
                    Unix.select
                        [Unix.descr_of_in_channel cin]
                        (if poll_o then [Unix.descr_of_out_channel cout] else [])
                        [Unix.descr_of_in_channel cerr] poll_tm_sec in
                if errs <> []
                then log_input_to_errlog (List.hd errs)
                else if poll_o && not poll_i && outs = [] && ins <> []
                then
                    (* yices produced too many warnings to stdout and thus
                       blocks its stdin.
                       Consume the text and spit it to the error log. *)
                    log_input_to_errlog (List.hd ins)
                else read_err := false;
                rs := ins;
                ws := outs
            done;
            (!rs, !ws)

        method consume_errors =
            let _, _ = self#poll false false in
            ()

        method poll_read = 
            let rs, _ = self#poll true false in
            if rs = []
            then raise (Communication_failure "Yices output is blocked")
            else List.hd rs

        method poll_write = 
            let _, ws = self#poll false true in
            if ws = []
            then raise (Communication_failure "Yices input is blocked")
            else List.hd ws

        (* as we communicate with yices via pipes, the program can be blocked
           if there is pending input/output on another channel.
           Thus, use select before an input/output.

           Did I started using OCaml to do low-level programming???
         *)
        method write_line s =
            let fd = self#poll_write in
            let len = String.length s in
            let pos = ref 0 in
            while !pos < len do
                let written = Unix.write fd s !pos (len - !pos) in
                if written = 0
                then raise (Communication_failure "Written 0 chars to the yices input");
                pos := !pos + written
            done

        method read_line =
            let start_tm = Unix.time () in (* raise the watchdog time *)
            let fd = self#poll_read in
            (* too inefficient??? *)
            let collected = ref [] in
            let collected_str () = String.concat "" (List.rev !collected) in
            let small_len = 100 in
            let small_buf = String.create small_len in
            let stop = ref false in
            while not !stop do
                let pos = ref 0 in
                let read = ref 1 in
                while not !stop && !read <> 0 && !pos < small_len do
                    begin
                        try read := Unix.read fd small_buf !pos 1;
                        with Invalid_argument s ->
                            self#consume_errors;
                            fprintf stderr "Read so far: %s\n" (collected_str ());
                            raise (Communication_failure "Yices output closed?")
                    end;
                    if !read > 0
                    then begin
                        let c = String.get small_buf !pos in
                        pos := !pos + 1;
                        if c == '\n'
                        then begin
                            stop := true;
                            pos := !pos - 1 (* strip '\n' *)
                        end
                    end
                done;
                if !pos > 0
                then collected := (String.sub small_buf 0 !pos) :: !collected;
                if not !stop
                then
                    let _ = self#poll_read in
                    if ((Unix.time ()) -. start_tm) > poll_tm_sec
                    then raise (Communication_failure "Yices is not responding")
            done;
            let out = collected_str () in
            log TRACE (sprintf "YICES: ^^^%s$$$\n" out);
            out

        method append cmd =
            if debug then printf "%s\n" cmd;
            self#write_line (sprintf "%s\n" cmd);
            fprintf clog "%s\n" cmd; flush clog

        method append_assert s =
            self#append (sprintf "(assert %s)" s)

        method append_var_def (v: var) =
            self#append (var_to_smt v)

        method comment (line: string) =
            self#append (";; " ^ line)

        method append_expr expr =
            let eid = ref 0 in
            let e_s = (expr_to_smt expr) in
            let is_comment = (String.length e_s) > 1
                    && e_s.[0] = ';' && e_s.[1] = ';' in
            if not is_comment
            then begin 
                if not collect_asserts
                then self#append (sprintf "(assert %s)" e_s)
                else begin
                    (* XXX: may block if the verbosity level < 2 *)
                    self#sync;
                    self#append (sprintf "(assert+ %s)" e_s);
                    let line = self#read_line in
                    if (Str.string_match (Str.regexp "id: \\([0-9]+\\)") line 0)
                    then
                        let id = int_of_string (Str.matched_group 1 line) in
                        eid := id
                end;
                !eid
            end else -1

        method push_ctx = self#append "(push)"

        method pop_ctx = self#append "(pop)"

        method sync =
            (* the solver can print more messages, thus, sync! *)
            self#append "(echo \"sync\\n\")";
            let stop = ref false in
            while not !stop do
                if "sync" = self#read_line then stop := true
            done

        method check =
            self#sync;
            self#append "(status)"; (* it can be unsat already *)
            flush cout;
            if not (self#is_out_sat true)
            then false
            else begin
                self#append "(check)";
                poll_tm_sec <- check_timeout_sec;
                flush cout;
                let res = self#is_out_sat false in
                poll_tm_sec <- timeout_sec;
                res
            end

        method set_need_evidence b =
            if b
            then self#append "(set-evidence! true)"
            else self#append "(set-evidence! false)"

        method get_evidence =
            (* same as sync but the lines are collected *)
            let lines = ref [] in
            self#append "(echo \"EOEV\\n\")"; flush cout;
            let stop = ref false in
            while not !stop do
                let line = self#read_line in
                if "EOEV" = line
                then stop := true
                else lines := line :: !lines
            done;
            List.rev !lines

        method get_collect_asserts = collect_asserts

        method set_collect_asserts b = collect_asserts <- b

        method get_unsat_cores =
            (* collect unsatisfiable cores *)
            let re = Str.regexp ".*unsat core ids: \\([ 0-9]+\\).*" in
            let cores = ref [] in
            self#append "(echo \"EOI\\n\")\n";
            let stop = ref false in
            while not !stop do
                let line = self#read_line in
                if Str.string_match re line 0
                then begin
                    let id_str = (Str.matched_group 1 line) in
                    let ids_as_str = (Str.split (Str.regexp " ") id_str) in
                    cores := (List.map int_of_string ids_as_str)
                end;

                stop := (line = "EOI")
            done;
            !cores

        method is_out_sat ignore_errors =
            let l = self#read_line in
            (*printf "%s\n" l;*)
            match l with
            | "sat" -> true
            | "ok" -> true
            | "unsat" -> false
            | _ -> if ignore_errors
                then false
                else raise (Smt_error (sprintf "yices: %s" l))

        method get_cin = cin
        method get_cout = cout
        method set_debug flag = debug <- flag
    end
;;

