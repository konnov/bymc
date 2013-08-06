(*
 * see pipeCmd.mli
 *)

open Printf

exception Comm_error of string

type state_t = Running | Stopping | Stopped

type writer_thread_state = {
    state: state_t ref;
    mutex: Mutex.t;
    pending_writes: string list ref;
    dirty: bool ref;
}

type cmd_stat = {
    pid: int;
    cin: in_channel;
    fdout: Unix.file_descr;
    err_filename: string;
    writer_st: writer_thread_state;
    writer_thr: Thread.t
}


(* the writes are handled by a separate thread, all writes are non-blocking *)
let write_handler (wts, fdout) =
    let sleep_tm = 0.001 in
    (* measure how many thread yields we can do in 1 msec *)
    let utime _ = (Unix.times ()).Unix.tms_utime in
    let start_tm = utime () in
    let max_yields = ref 1 in
    while (((utime ()) -. start_tm) < sleep_tm) && (!max_yields < max_int / 2)
    do
        for i = 1 to !max_yields do
            Thread.yield ()
        done;
        max_yields := !max_yields * 2
    done;
    printf "[writer thread]: about %d yields in 1 msec\n" !max_yields;
    (* process the input lines *)
    let yields = ref 0 in
    while !(wts.state) <> Stopping do
        (* fprintf stderr ".\n"; flush stderr; *)
        if !(wts.dirty) (* don't bother CPU with redundant mutex locks *)
        then begin
            Mutex.lock wts.mutex;
            let lines =
                match !(wts.pending_writes) with
                | _ :: _ as l ->
                    begin
                        wts.pending_writes := [];
                        List.rev l (* the insertion was in the inverse order *)
                    end
                | [] -> []
            in
            Mutex.unlock wts.mutex;
            wts.dirty := false;
            yields := 0; (* maximum processing speed again *)
            (* now write the line to the output, might be blocked *)
            (*fprintf stderr "write: %s\n" line; flush stderr;*)
            let writeln l = 
                let ln = l ^ "\n" in
                try
                    let _ = Unix.write fdout ln 0 (String.length ln) in ()
                with Unix.Unix_error (e, op, msg) ->
                begin
                    fprintf stderr "[writer thread] %s: on '%s'"
                        (Unix.error_message e) ln;
                    Pervasives.exit 3
                end
            in
            List.iter writeln lines
        end;
        (* idle a little bit an then sleep *)
        yields := !yields + 1;
        if !yields > !max_yields
        then Thread.delay sleep_tm  (* sleep for 1 msec *)
        else Thread.yield () (* else busy waiting several times *)
    done;
    wts.state := Stopped


let writeline st s =
    Mutex.lock st.writer_st.mutex;
    st.writer_st.dirty := true;
    st.writer_st.pending_writes := s :: !(st.writer_st.pending_writes);
    Mutex.unlock st.writer_st.mutex


let readline st =
    try
        input_line st.cin
    with End_of_file ->
        raise (Comm_error
            ("Process terminated prematurely, see: " ^ st.err_filename))


let create prog args err_filename =
    (* Unix.open_process_full is not flexible enough, i.e., if it is executed
       with the wrong filename, then it reports only to stderr. In this case,
       it is nearly impossible to distinguish between an error situation and a
       verbose input by programs like Yices.  Thus, use the standard Unix
       approach, even in OCaml.
     *)
    let in_pipe_i, in_pipe_o = Unix.pipe () in
    let out_pipe_i, out_pipe_o = Unix.pipe () in
    (* open file to redirect the error output *)
    let fderr =
        Unix.openfile err_filename
            [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] 0o600 in
    let pid = Unix.fork () in
    if pid = 0
    then begin
        (* the child *)
        Unix.dup2 in_pipe_o Unix.stdout;
        Unix.close in_pipe_i; Unix.close in_pipe_o; 
        Unix.dup2 out_pipe_i Unix.stdin;
        Unix.close out_pipe_i; Unix.close out_pipe_o; 
        Unix.dup2 fderr Unix.stderr;
        let exec _ =
            let _ = Unix.execvp prog (Array.append [|prog|] args) in
            () in
        (* exit, if an error occurs *)
        let _ = Unix.handle_unix_error exec () in ()
    end else begin
        (* the parent *)
        Unix.close in_pipe_o; 
        Unix.close out_pipe_i;
        Unix.close fderr
    end;
    let writer_state = {
        state = ref Running; dirty = ref false;
        mutex = Mutex.create (); pending_writes = ref []
    } in
    let writer_thread = Thread.create write_handler (writer_state, out_pipe_o)
    in
    let cin = Unix.in_channel_of_descr in_pipe_i in
    set_binary_mode_in cin false;
    {
        pid = pid; (*fdin = in_pipe_i;*) cin = cin; fdout = out_pipe_o;
        err_filename = err_filename;
        writer_st = writer_state; writer_thr = writer_thread
    }


let destroy st =
    st.writer_st.state := Stopping;
    Thread.join st.writer_thr;
    close_in st.cin;
    Unix.close st.fdout;
    let _ = Unix.waitpid [] st.pid in
    true

