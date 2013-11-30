open OUnit
open Printf

open Accums
open Cfg
open Smt
open Spin
open SpinIr
open SpinIrImp
open Ssa


let setup _ =
    ()

let teardown _ =
    ()


let test_trans_proc_decl _ =
    assert_failure "foo!"

let suite = "ssa-suite" >:::
    [
        "test_trans_proc_decl"
            >:: (bracket setup test_trans_proc_decl teardown)
    ]

