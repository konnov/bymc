open OUnit
open Printf

open Accums


let test_fuse_several _ =
    assert_failure "nothing here"


let suite = "symbSkel-suite" >:::
    [
        "test_fuse_several" >:: test_fuse_several
    ]

