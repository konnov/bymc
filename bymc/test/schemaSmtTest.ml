open Batteries

open OUnit
open Printf

open Accums
open SchemaSmt

let save_cex _ =
    let cex = {
        C.f_form_name = "corr";
        C.f_loop_index = 0;
        C.f_init_state = StrMap.add "y" 2 (StrMap.singleton "x" 1);
        C.f_moves = [
            { C.f_rule_no = 0; f_accel = 22 };
            { C.f_rule_no = 1; f_accel = 33 };
        ];
        C.f_iorder = [1; 2; 3];
    }
    in
    let expected =
        "((spec corr) (loop 0) (init ((x 1) (y 2))) (moves ((0 22) (1 33)))\n"
        ^ " (iorder (1 2 3)))\n"
    in
    C.save_cex "cex.scm" cex;
    let input = BatFile.open_in "cex.scm" in
    let result = BatIO.read_all input in
    BatIO.close_in input;
    assert_equal expected result
        ~msg:(sprintf "Expected '%s', found '%s'" expected result)


let load_cex _ =
    let text =
        "((spec corr) (loop 0) (init ((x 1) (y 2))) (moves ((0 22) (1 33)))\n"
        ^ " (iorder (1 2 3)))\n"
    in
    let output = BatFile.open_out ~mode:[`create; `trunc] "cex.scm" in
    fprintf output "%s\n" text;
    BatIO.close_out output;
    let result = C.load_cex "cex.scm" in
    let expected = {
        C.f_form_name = "corr";
        C.f_loop_index = 0;
        C.f_init_state = StrMap.add "y" 2 (StrMap.singleton "x" 1);
        C.f_moves = [
            { C.f_rule_no = 0; f_accel = 22 };
            { C.f_rule_no = 1; f_accel = 33 };
        ];
        C.f_iorder = [1; 2; 3];
    }
    in
    assert_equal expected result ~msg:("Unexpected counterexample")



let suite = "schemaSmt-suite" >:::
    [
        "save_cex" >::save_cex;
        "load_cex" >::load_cex;
    ]

