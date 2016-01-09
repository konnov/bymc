open Batteries

open OUnit
open Printf

open Accums

open Poset


(* wrap a test with this function to see the tracing output *)
let with_tracing test_fun arg =
    Debug.enable_tracing () Trc.pos;
    let cleanup _ = Debug.disable_tracing () Trc.pos in
    finally cleanup test_fun arg


let rec fact n =
    (* finally, I have found some use of it :-) *)
    if n <= 1
    then 1
    else n * fact (n - 1)


let assert_iter_eq expected iter =
    let order = Array.to_list (linord_iter_get iter) in
    assert_equal expected order
        ~msg:(sprintf "Expected order = [%s], found [%s]"
            (str_join ", " (List.map int_s expected))
            (str_join ", " (List.map int_s order)))


let assert_iter_end iter =
    if not (linord_iter_is_end iter)
    then let order = Array.to_list (linord_iter_get iter) in
        assert_equal true (linord_iter_is_end iter)
            ~msg:(sprintf "Expected end iterator, found: [%s]"
                (str_join ", " (List.map int_s order)))


let assert_iter_list expected_list iter =
    let each order =
        assert_iter_eq order iter;
        linord_iter_next iter;
    in
    List.iter each expected_list;
    assert_iter_end iter


let assert_no_dups iter =
    let hits = Hashtbl.create 1024 in
    Hashtbl.add hits (linord_iter_get iter) 1;
    while not (linord_iter_is_end iter) do
        let order = linord_iter_get iter in
        linord_iter_next iter;
        if not (linord_iter_is_end iter)
        then begin
            assert_bool
                (sprintf "Found a duplicate: [%s]"
                    (str_join ", " (List.map int_s (BatArray.to_list order))))
                (not (Hashtbl.mem hits order));
            Hashtbl.add hits (linord_iter_get iter) 1;
        end
    done


let assert_iter_count nexpected iter =
    let count = ref 0 in
    if not (linord_iter_is_end iter)
    then count := !count + 1;

    while not (linord_iter_is_end iter) do
        let order = linord_iter_get iter in
        linord_iter_next iter;
        if not (linord_iter_is_end iter)
        then count := !count + 1;
    done;

    assert_equal nexpected !count
        ~msg:(sprintf "Expected %d elements, found: %d" nexpected !count)




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


let test_linord_iter_next2 _ =
    (*        (0)  (1)       *)
    let iter = linord_iter_first 2 [] in
    assert_iter_eq [0; 1] iter;
    linord_iter_next iter;
    assert_equal false (linord_iter_is_end iter)
        ~msg:(sprintf "Unexpected end iterator");
    assert_iter_eq [1; 0] iter;
    linord_iter_next iter;
    assert_equal true (linord_iter_is_end iter)
        ~msg:(sprintf "Expected end iterator")


let test_linord_iter_next4x4 _ =
    (*        (2)  (3)
               | \/ |
               | /\ |
              (0)  (1)       *)
    let iter = linord_iter_first 4 [(0, 2); (1, 2); (0, 3); (1, 3)] in
    assert_iter_list [
        [0; 1; 2; 3];
        [1; 0; 2; 3];
        [1; 0; 3; 2];
        [0; 1; 3; 2];
    ] iter
   

let test_linord_iter_next4x6 _ =
    (*        (2)  (3)
               |    |
               |    |
              (0)  (1)       *)
    let iter = linord_iter_first 4 [(0, 2); (1, 3)] in
    assert_iter_list [
        [0; 1; 2; 3];
        [0; 2; 1; 3];
        [1; 0; 2; 3];
        [1; 0; 3; 2];
        [1; 3; 0; 2];
        [0; 1; 3; 2];
    ] iter
 

let test_linord_iter_next3x2 _ =
    (*          (2)
                / \ 
               /   \
              (0) (1)       *)
    let iter = linord_iter_first 3 [(0, 2); (1, 2)] in
    assert_iter_list [
        [0; 1; 2;];
        [1; 0; 2;];
    ] iter


let test_linord_iter_next4x2 _ =
    (*          (3)
                / \ 
               /   \
             (1)   (2)
               \   /
                \ /
                (0)
     *)
    let iter = linord_iter_first 4 [(0, 1); (0, 2); (1, 3); (2, 3)] in
    assert_iter_list [
        [0; 1; 2; 3];
        [0; 2; 1; 3];
    ] iter


let test_linord_iter_next7 _ =
    (*          (6)
                / \ 
               /   \
             (4)   (5)
               \   /
                \ /
                (3)
                / \ 
               /   \
             (1)   (2)
               \   /
                \ /
                (0)
     *)
    let iter = linord_iter_first 7
        [(0, 1); (0, 2); (1, 3); (2, 3); (3, 4); (3, 5); (4, 6); (5, 6)]
    in
    assert_iter_list [
        [0; 1; 2; 3; 4; 5; 6];
        [0; 2; 1; 3; 4; 5; 6];
        [0; 2; 1; 3; 5; 4; 6];
        [0; 1; 2; 3; 5; 4; 6];
    ] iter


let test_linord_iter_next6 _ =
    (*          (5)
                / \ 
               /   \
             (3)   (4)
              |\   /|
              | \ / |
              |  X  |
              | / \ |
              |/   \|
             (1)   (2)
               \   /
                \ /
                (0)
     *)
    let iter = linord_iter_first 6
        [(0, 1); (0, 2); (1, 3); (2, 4); (1, 4); (2, 3); (3, 5); (4, 5)]
    in
    assert_iter_list [
        [0; 1; 2; 3; 4; 5];
        [0; 2; 1; 3; 4; 5];
        [0; 2; 1; 4; 3; 5];
        [0; 1; 2; 4; 3; 5];
    ] iter


let test_linord_iter_next_3_lines _ =
    (*        (1)  (3)  (5)
               |    |    |
               |    |    |
              (0)  (2)  (4)   *)
    let iter = linord_iter_first 6 [(0, 1); (2, 3); (4, 5);] in
    assert_iter_list [
        [0; 2; 1; 3; 4; 5]; [0; 1; 2; 3; 4; 5]; [0; 1; 4; 2; 3; 5];
        [0; 1; 2; 4; 3; 5]; [0; 2; 1; 4; 3; 5]; [0; 2; 4; 1; 3; 5];
        [0; 4; 2; 1; 3; 5]; [4; 0; 2; 1; 3; 5]; [4; 2; 0; 1; 3; 5];
        [2; 4; 0; 1; 3; 5]; [2; 0; 4; 1; 3; 5]; [2; 0; 1; 4; 3; 5];
        [2; 0; 1; 3; 4; 5]; [2; 0; 3; 1; 4; 5]; [2; 3; 0; 1; 4; 5];
        [2; 3; 4; 0; 1; 5]; [2; 3; 0; 4; 1; 5]; [2; 0; 3; 4; 1; 5];
        [2; 0; 3; 4; 5; 1]; [2; 3; 0; 4; 5; 1]; [0; 2; 3; 4; 5; 1];
        [0; 2; 4; 3; 5; 1]; [0; 4; 2; 3; 5; 1]; [4; 0; 2; 3; 5; 1];
        [0; 4; 5; 2; 3; 1]; [4; 0; 5; 2; 3; 1]; [4; 5; 0; 2; 3; 1];
        [4; 0; 2; 5; 3; 1]; [0; 4; 2; 5; 3; 1]; [0; 2; 4; 5; 3; 1];
        [2; 0; 4; 5; 3; 1]; [2; 4; 0; 5; 3; 1]; [4; 2; 0; 5; 3; 1];
        [4; 2; 3; 5; 0; 1]; [2; 4; 3; 5; 0; 1]; [2; 4; 3; 0; 5; 1];
        [4; 2; 3; 0; 5; 1]; [4; 2; 0; 3; 5; 1]; [2; 4; 0; 3; 5; 1];
        [2; 0; 4; 3; 5; 1]; [2; 0; 4; 3; 1; 5]; [2; 4; 0; 3; 1; 5];
        [4; 2; 0; 3; 1; 5]; [4; 0; 2; 3; 1; 5]; [0; 4; 2; 3; 1; 5];
        [0; 2; 4; 3; 1; 5]; [0; 2; 3; 4; 1; 5]; [0; 2; 3; 1; 4; 5];
    ] iter


let test_linord_iter_next_3_lines_no_dups _ =
    (*        (1)  (3)  (5)
               |    |    |
               |    |    |
              (0)  (2)  (4)   *)
    let iter = linord_iter_first 6 [(0, 1); (2, 3); (4, 5);] in
    assert_no_dups iter


let test_linord_iter_next_2_lines_1_dot _ =
    (*        (1)  (3)
               |    |
               |    |
              (0)  (2)  (4)   *)
    let iter = linord_iter_first 5 [(0, 1); (2, 3); ] in
    assert_iter_list [
        [0; 2; 1; 3; 4]; [0; 1; 2; 3; 4]; [0; 1; 4; 2; 3];
        [0; 1; 2; 4; 3]; [0; 2; 1; 4; 3]; [0; 2; 4; 1; 3];
        [0; 4; 2; 1; 3]; [4; 0; 2; 1; 3]; [4; 2; 0; 1; 3];
        [2; 4; 0; 1; 3]; [2; 0; 4; 1; 3]; [2; 0; 1; 4; 3];
        [2; 0; 1; 3; 4]; [2; 0; 3; 1; 4]; [2; 3; 0; 1; 4];
        [2; 3; 4; 0; 1]; [2; 3; 0; 4; 1]; [2; 0; 3; 4; 1];
        [2; 0; 4; 3; 1]; [2; 4; 0; 3; 1]; [4; 2; 0; 3; 1];
        [4; 0; 2; 3; 1]; [0; 4; 2; 3; 1]; [0; 2; 4; 3; 1];
        [0; 2; 3; 4; 1]; [0; 2; 3; 1; 4];
    ] iter;
    let iter = linord_iter_first 5 [(0, 1); (2, 3); ] in
    assert_no_dups iter


let test_linord_iter_next_3_dots _ =
    let iter = linord_iter_first 3 [] in
    assert_iter_count (fact 3) iter


let test_linord_iter_next_4_dots _ =
    let mk_iter _ = linord_iter_first 4 [] in
    assert_no_dups (mk_iter ());
    assert_iter_count (fact 4) (mk_iter ())


let test_linord_iter_next_5_dots _ =
    let mk_iter _ = linord_iter_first 5 [] in
    assert_iter_count (fact 5) (mk_iter ());
    assert_no_dups (mk_iter ())


let test_linord_iter_next_7_dots _ =
    let mk_iter _ = linord_iter_first 7 [] in
    assert_no_dups (mk_iter ());
    assert_iter_count (fact 7) (mk_iter ())


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
        "test_linord_iter_next2" >:: test_linord_iter_next2;
        "test_linord_iter_next4x4" >:: test_linord_iter_next4x4;
        "test_linord_iter_next4x6" >:: test_linord_iter_next4x6;
        "test_linord_iter_next4x2" >:: test_linord_iter_next4x2;
        "test_linord_iter_next7" >:: test_linord_iter_next7;
        "test_linord_iter_next6" >:: test_linord_iter_next6;
        "test_linord_iter_next_3_dots" >:: test_linord_iter_next_3_dots;
        "test_linord_iter_next_4_dots" >:: test_linord_iter_next_4_dots;
        "test_linord_iter_next_5_dots" >:: (with_tracing test_linord_iter_next_5_dots);
        (*
        "test_linord_iter_next_3_lines" >:: test_linord_iter_next_3_lines;
        "test_linord_iter_next_3_lines_no_dups"
            >:: test_linord_iter_next_3_lines_no_dups;
        "test_linord_iter_next_2_lines_1_dot"
            >:: test_linord_iter_next_2_lines_1_dot;
        "test_linord_iter_next_7_dots" >:: test_linord_iter_next_7_dots;
        *)
    ]

