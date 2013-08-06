open OUnit
open Printf

open PipeCmd

let test_create _ =
    let _ = PipeCmd.create "cat" [| |] "cmd.log" in
    () (* no exceptions *)


let test_create_non_existent _ =
    let crt _ =
        let s = PipeCmd.create "this-file-does-not-exist" [| |] "cmd.log" in
        (* we can detect the premature termination only by enquiring channels *)
        PipeCmd.writeline s "a";
        let _ = PipeCmd.readline s in
        ()
    in
    assert_raises
        (Comm_error "Process terminated prematurely, see: cmd.log") crt


let test_destroy _ =
    let s = PipeCmd.create "cat" [| |] "cmd.log" in
    assert_equal true (PipeCmd.destroy s)


let test_destroy_twice _ =
    let s = PipeCmd.create "cat" [| |] "cmd.log" in
    assert_equal true (PipeCmd.destroy s);
    let destr _ = PipeCmd.destroy s in
    assert_raises (Unix.Unix_error (Unix.EBADF, "close", "")) destr


let test_writeline _ =
    let s = PipeCmd.create "cat" [| |] "cmd.log" in
    PipeCmd.writeline s "abcd"


let test_writeline_readline _ =
    let s = PipeCmd.create "cat" [| |] "cmd.log" in
    PipeCmd.writeline s "bcde";
    let str = PipeCmd.readline s in
    assert_equal "bcde" str


let test_writeline_readline_10000 _ =
    let s = PipeCmd.create "cat" [| |] "cmd.log" in
    let mk_s n = String.make (1 + n) 'z' in
    for i = 0 to 10000 do
        PipeCmd.writeline s (mk_s i);
    done;
    for i = 0 to 10000 do
        let str = PipeCmd.readline s in
        assert_equal (mk_s i) str
    done


let test_writeline_readline_100000 _ =
    let s = PipeCmd.create "cat" [| |] "cmd.log" in
    for i = 0 to 100000 do
        PipeCmd.writeline s "abc";
    done;
    for i = 0 to 10000 do
        let str = PipeCmd.readline s in
        assert_equal "abc" str
    done


let suite = "pipeCmd-suite" >:::
    ["test_create" >:: test_create;
     "test_create_non_existent" >:: test_create_non_existent;
     (*
     "test_destroy" >:: test_destroy;
     "test_destroy_twice" >:: test_destroy_twice;
     *)
     "test_writeline" >:: test_writeline;
     "test_writeline_readline" >:: test_writeline_readline;
     "test_writeline_readline_10000" >:: test_writeline_readline_10000;
     "test_writeline_readline_100000" >:: test_writeline_readline_100000;
    ]
