open OUnit
open Printf

open Accums

open Poset

let test_mk_po_matrix _ =
    let matrix = mk_po_matrix 3 [(0, 1); (0, 2)] in
    assert_equal 3 (Array.length matrix);
    assert_equal 3 (Array.length matrix.(0));
    assert_equal 3 (Array.length matrix.(1));
    assert_equal 3 (Array.length matrix.(2))


let test_mk_po_matrix_out_of_range _ =
    let expected_msg = "Element is out of range: 4" in
    try
        ignore (mk_po_matrix 3 [(0, 1); (0, 4)]);
        assert_failure ("Expected: " ^ expected_msg)
    with Poset_error msg ->
        assert_equal expected_msg msg
            ~msg:(sprintf "Expected %s, found '%s'" expected_msg msg)


let test_mk_po_matrix_reflexive _ =
    let expected_msg = "Anti-reflexivity violated: (1, 1)" in
    try
        ignore (mk_po_matrix 3 [(0, 1); (1, 1)]);
        assert_failure ("Expected: " ^ expected_msg)
    with Poset_error msg ->
        assert_equal expected_msg msg
            ~msg:(sprintf "Expected %s, found '%s'" expected_msg msg)


let test_mk_po_matrix_antisymmetric _ =
    let expected_msg = "Anti-symmetry violated: (2, 1) and (1, 2)" in
    try
        ignore (mk_po_matrix 3 [(1, 2); (0, 1); (2, 1)]);
        assert_failure ("Expected: " ^ expected_msg)
    with Poset_error msg ->
        assert_equal expected_msg msg
            ~msg:(sprintf "Expected %s, found '%s'" expected_msg msg)


let test_mk_po_matrix_transitive _ =
    let mx = mk_po_matrix 3 [(0, 1); (1, 2)] in
    assert_bool ("0 must precede 2") (Poset.prec mx 0 2)


let test_mk_po_matrix_antisymmetric2 _ =
    let expected_msg = "Anti-symmetry violated: (2, 0) and (0, 2)" in
    try
        ignore (mk_po_matrix 3 [(1, 2); (0, 1); (2, 0)]);
        assert_failure ("Expected: " ^ expected_msg)
    with Poset_error msg ->
        assert_equal expected_msg msg
            ~msg:(sprintf "Expected %s, found '%s'" expected_msg msg)


let suite = "poset-suite" >:::
    [
        "test_mk_po_matrix" >:: test_mk_po_matrix;
        "test_mk_po_matrix_out_of_range" >:: test_mk_po_matrix_out_of_range;
        "test_mk_po_matrix_reflexive" >:: test_mk_po_matrix_reflexive;
        "test_mk_po_matrix_antisymmetric" >:: test_mk_po_matrix_antisymmetric;
        "test_mk_po_matrix_antisymmetric2" >:: test_mk_po_matrix_antisymmetric2;
        "test_mk_po_matrix_transitive" >:: test_mk_po_matrix_transitive;
    ]

