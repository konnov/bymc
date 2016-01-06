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


let test_linord_iter_first_singleton _ =
    let iter = linord_iter_first 1 [] in
    let init_order = Array.to_list (linord_iter_get iter) in
    let expected = [0] in
    assert_equal expected init_order
        ~msg:(sprintf "Expected [%s], found [%s]"
            (str_join ", " (List.map int_s expected))
            (str_join ", " (List.map int_s init_order)))


let test_linord_iter_first_pair _ =
    let iter = linord_iter_first 2 [(1, 0)] in
    let init_order = Array.to_list (linord_iter_get iter) in
    let expected = [1; 0] in
    assert_equal expected init_order
        ~msg:(sprintf "Expected [%s], found [%s]"
            (str_join ", " (List.map int_s expected))
            (str_join ", " (List.map int_s init_order)))


let test_linord_iter_first9 _ =
    let iter =
        linord_iter_first 9
        [(2, 1); (3, 1); (1, 4); (0, 4); (5, 6); (6, 7); (4, 8); (7, 8)] in
    let init_order = Array.to_list (linord_iter_get iter) in
    let expected = [0; 2; 3; 5; 1; 6; 4; 7; 8] in
    assert_equal expected init_order
        ~msg:(sprintf "Expected [%s], found [%s]"
            (str_join ", " (List.map int_s expected))
            (str_join ", " (List.map int_s init_order)))


let suite = "poset-suite" >:::
    [
        "test_mk_po_matrix" >:: test_mk_po_matrix;
        "test_mk_po_matrix_out_of_range" >:: test_mk_po_matrix_out_of_range;
        "test_mk_po_matrix_reflexive" >:: test_mk_po_matrix_reflexive;
        "test_mk_po_matrix_antisymmetric" >:: test_mk_po_matrix_antisymmetric;
        "test_mk_po_matrix_antisymmetric2" >:: test_mk_po_matrix_antisymmetric2;
        "test_mk_po_matrix_transitive" >:: test_mk_po_matrix_transitive;
        "test_linord_iter_first_singleton" >:: test_linord_iter_first_singleton;
        "test_linord_iter_first_pair" >:: test_linord_iter_first_pair;
        "test_linord_iter_first9" >:: test_linord_iter_first9;
    ]

