open OUnit

open PipeCmd

let test_create _ =
    let s = PipeCmd.create "cat" [| |] in
    () (* no exceptions *)


let suite = "pipeCmd-suite" >::: ["test_create" >:: test_create]

