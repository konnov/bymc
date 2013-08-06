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
    let tries = ref 0 in
    while !(wts.state) <> Stopping do
        (* fprintf stderr ".\n"; flush stderr; *)
        Mutex.lock wts.mutex;
        let line =
            match !(wts.pending_writes) with
            | hd :: tl ->
                begin
                    wts.pending_writes := tl;
                    hd
                end
            | [] ->
                ""
        in
        Mutex.unlock wts.mutex;
        if line <> ""
        then begin
            tries := 0; (* maximum processing speed again *)
            (* now write the line to the output, might be blocked *)
            (*fprintf stderr "write: %s\n" line; flush stderr;*)
            let linen = line ^ "\n" in
            let written =
                Unix.write fdout linen 0 (String.length linen) in
            if written < 0
            then begin
                fprintf stderr "write_handler: write error!\n";
                exit 3
            end
        end else begin
            (* no actual data to write, idle a little bit an then sleep *)
            tries := !tries + 1;
            if !tries > 100
            then Thread.delay 0.1  (* sleep for 100 msec *)
            else if !tries > 10
            then Thread.delay 0.01 (* sleep for 10 msec *)
            (* else busy waiting *)
        end
    done;
    wts.state := Stopped


let writeline st s =
    Mutex.lock st.writer_st.mutex;
    st.writer_st.pending_writes :=
        (* TODO: use two lists: one for writing, one for reading? *)
        List.rev (s :: (List.rev !(st.writer_st.pending_writes)));
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
        state = ref Running;
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
    close_in st.cin;
    Unix.close st.fdout;
    let _ = Unix.waitpid [] st.pid in
    st.writer_st.state := Stopping;
    Thread.join st.writer_thr;
    true

