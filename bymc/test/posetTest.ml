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
    while not (linord_iter_is_end iter) do
        let order = linord_iter_get iter in
        let key = str_join "," (List.map int_s (BatArray.to_list order)) in
        assert_bool
            (sprintf "Found a duplicate: [%s]" key)
            (not (Hashtbl.mem hits key));
        Hashtbl.add hits key 1;
        linord_iter_next iter;
    done


let assert_order_preserved iter =
    let mx = linord_iter_get_matrix iter in
    let pr order =
        str_join "" (List.map int_s order)
    in
    let asrt order a b =
        assert_bool
            (sprintf "Found wrong order %d < %d: [%s]" a b (pr order))
            (not (prec mx b a ));
        assert_bool
            (sprintf "Corrupted order, contains %d two times" a)
            (a != b);
    in
    while not (linord_iter_is_end iter) do
        let order = BatArray.to_list (linord_iter_get iter) in
        let rec check = function
            | [] -> ()

            | a :: tl ->
                List.iter (asrt order a) tl;
                check tl
        in
        check order;
        linord_iter_next iter;
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


let mk_binary_level_poset height =
    (* perhaps, it is not very efficient, but it was easy to write *)
    let rec mk prec start level level_cnt =
        if level > height
        then (start + level_cnt, prec)
        else let beyond = start + level_cnt in
            let connections = BatList.cartesian_product
                (BatList.of_enum (beyond --^ (beyond + 2 * level_cnt)))
                (BatList.of_enum (start --^ beyond))
            in
            mk (prec @ connections) beyond (level + 1) (2 * level_cnt)
    in
    mk [] 0 1 1


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


let test_linord_iter_next3 _ =
    (*        (2)
               |
               |
              (0)  (1)       *)
    let iter = linord_iter_first 3 [(0, 2)] in
    assert_iter_list [
        [0; 1; 2];
        [0; 2; 1];
        [1; 0; 2];
    ] iter


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
    let mk_iter _ = linord_iter_first 6 [(0, 1); (2, 3); (4, 5);] in
    assert_no_dups (mk_iter ());
    assert_iter_count 90 (mk_iter ());
    assert_order_preserved (mk_iter ())


let test_linord_iter_next_2_lines_1_dot _ =
    (*        (1)  (3)
               |    |
               |    |
              (0)  (2)  (4)   *)
    let mk_iter () = linord_iter_first 5 [(0, 1); (2, 3)] in
    assert_no_dups (mk_iter ());
    assert_iter_count 30 (mk_iter ());
    assert_order_preserved (mk_iter ())


let test_linord_iter_next_count_2_lines_2_dots _ =
    (*
              (1)  (3)  (5)
               |    |
               |    |
              (0)  (2)  (4)
     *)
    (* collect what the algorithm thinks should be the linearizations *)
    let iter = linord_iter_first 6 [(0, 1); (2, 3)] in
    let hits = Hashtbl.create 1024 in
    while not (linord_iter_is_end iter) do
        let order = linord_iter_get iter in
        let key = str_join "," (List.map int_s (BatArray.to_list order)) in
        Hashtbl.add hits key 1;
        linord_iter_next iter;
    done;
    Debug.trace Trc.pos (fun _ -> sprintf "-------------------------------\n");
    (* collect the linearizations by brute force and check,
       whether some orders are missing
      *)
    let is_invalid pair_fun order =
        let rec check = function
        | [] -> false

        | a :: tl ->
            if List.exists (pair_fun a) tl
            then true
            else check tl
        in
        check order
    in
    let iter = linord_iter_first 6 [] in

    let count = ref 0 in
    while not (linord_iter_is_end iter) do
        let order = BatArray.to_list (linord_iter_get iter) in
        if not (is_invalid (fun a b -> a = 1 && b = 0 || a = 3 && b = 2) order)
        then begin
            let key = str_join "," (List.map int_s order) in
            assert_bool
                (sprintf "The linear order is missing: [%s]" key)
                (Hashtbl.mem hits key);
            count := 1 + !count;
        end;
        linord_iter_next iter;
    done;
    let expected_count = 180 in
    assert_equal expected_count !count
        ~msg:(sprintf "Expected %d elements, found %d" expected_count !count)


let test_linord_iter_next_2_lines_4_dots _ =
    (*
              (1)  (3)  (5)
               |    |
               |    |
              (0)  (2)  (4)
     *)
    (* collect what the algorithm thinks should be the linearizations *)
    let iter = linord_iter_first 8 [(0, 1); (2, 3)] in
    let hits = Hashtbl.create 1024 in
    while not (linord_iter_is_end iter) do
        let order = linord_iter_get iter in
        let key = str_join "," (List.map int_s (BatArray.to_list order)) in
        Hashtbl.add hits key 1;
        linord_iter_next iter;
    done;
    Debug.trace Trc.pos (fun _ -> sprintf "-------------------------------\n");
    let expected_count = 10080 in
    let count = Hashtbl.length hits in
    assert_equal expected_count count
        ~msg:(sprintf "Expected %d elements, found %d" expected_count count);

    if (false) then begin
        (* if the above assertion fails, use the following code to find the
           missing elements *)

        (* collect the linearizations by brute force and check,
           whether some orders are missing
          *)
        let is_invalid pair_fun order =
            let rec check = function
            | [] -> false

            | a :: tl ->
                if List.exists (pair_fun a) tl
                then true
                else check tl
            in
            check order
        in
        let iter = linord_iter_first 8 [] in

        let count = ref 0 in
        while not (linord_iter_is_end iter) do
            let order = BatArray.to_list (linord_iter_get iter) in
            if not (is_invalid (fun a b -> a = 1 && b = 0 || a = 3 && b = 2) order)
            then begin
                let key = str_join "," (List.map int_s order) in
                assert_bool
                    (sprintf "The linear order is missing: [%s]" key)
                    (Hashtbl.mem hits key);
                count := 1 + !count;
            end;
            linord_iter_next iter;
        done;
        let expected_count = 10080 in
        assert_equal expected_count !count
            ~msg:(sprintf "Expected %d elements, found %d" expected_count !count)
    end


let test_linord_iter_next_2_lines_2_dots _ =
    (*        (1)  (3)  (5)
               |    |
               |    |
              (0)  (2)  (4)   *)
    let mk_iter () = linord_iter_first 6 [(0, 1); (2, 3)] in
    assert_no_dups (mk_iter ());
    assert_order_preserved (mk_iter ());
    assert_iter_count 180 (mk_iter ())


let test_linord_iter_next_1_line_14 _ =
    (* a very long line of 67 nodes *)
    let rec mk_line n =
        if n > 1
        then (n - 2, n - 1) :: (mk_line (n - 1))
        else []
    in
    let n = 14 in
    let mk_iter () = linord_iter_first n (mk_line n) in
    assert_no_dups (mk_iter ());
    assert_order_preserved (mk_iter ());
    assert_iter_count 1 (mk_iter ())


let test_linord_iter_next_1_line_13 _ =
    (* a very long line of 66 nodes *)
    let rec mk_line n =
        if n > 1
        then (n - 1, n - 2) :: (mk_line (n - 1))
        else []
    in
    let n = 13 in
    let mk_iter () = linord_iter_first n (mk_line n) in
    assert_no_dups (mk_iter ());
    assert_order_preserved (mk_iter ());
    assert_iter_count 1 (mk_iter ())



let test_linord_iter_next_3_dots _ =
    let mk_iter _ = linord_iter_first 3 [] in
    assert_no_dups (mk_iter ());
    assert_iter_count (fact 3) (mk_iter ());
    assert_order_preserved (mk_iter ())


let test_linord_iter_next_4_dots _ =
    let mk_iter _ = linord_iter_first 4 [] in
    assert_no_dups (mk_iter ());
    assert_iter_count (fact 4) (mk_iter ());
    assert_order_preserved (mk_iter ())


let test_linord_iter_next_5_dots _ =
    let mk_iter _ = linord_iter_first 5 [] in
    assert_iter_count (fact 5) (mk_iter ());
    assert_no_dups (mk_iter ());
    assert_order_preserved (mk_iter ())


let test_linord_iter_next_x_fighter _ =
    (*             
             (3)   (4)
               \   / 
                \ /  
                (2)  
                / \  
               /   \ 
             (0)   (1)
     *)
    let mk_iter _ = linord_iter_first 5 [(0, 2); (1, 2); (2, 3); (2, 4)] in
    assert_iter_count 4 (mk_iter ());
    assert_no_dups (mk_iter ());
    assert_order_preserved (mk_iter ())


let test_linord_iter_next_pyramide _ =
    (*             
             (4)     (5)
              | \   / |
              |  \ /  |
              |   X   | 
              |  /|\  |   
              | / | \ |  
             (0) (1) (3)
     *)
    let mk_iter _ =
        linord_iter_first 5 [(0, 3); (0, 4); (1, 3); (1, 4); (2, 3); (2, 4)] in
    assert_iter_count 12 (mk_iter ());
    assert_no_dups (mk_iter ());
    assert_order_preserved (mk_iter ())


let test_linord_iter_next_7_dots _ =
    let mk_iter _ = linord_iter_first 7 [] in
    assert_no_dups (mk_iter ());
    assert_iter_count (fact 7) (mk_iter ());
    assert_order_preserved (mk_iter ())


let test_linord_iter_next_8_dots _ =
    let mk_iter _ = linord_iter_first 8 [] in
    assert_no_dups (mk_iter ());
    assert_iter_count (fact 8) (mk_iter ());
    assert_order_preserved (mk_iter ())


let test_linord_next_broom _ =
    (*             
             (3)(4)(5)
               \ | / 
                \|/  
                (2)  
                 | 
                (1) 
                 |
                (0)
     *)
    let mk_iter _ = linord_iter_first 6 [(0, 1); (1, 2); (2, 3); (2, 4); (2, 5)] in
    assert_iter_count (fact 3) (mk_iter ());
    assert_no_dups (mk_iter ());
    assert_order_preserved (mk_iter ())


let test_linord_iter_next_broom_inverse _ =
    (*             
                (5)  
                 | 
                (4) 
                 |
                (3)
                /|\  
               / | \ 
             (0)(1)(2)
     *)
    let mk_iter _ = linord_iter_first 6 [(0, 3); (1, 3); (2, 3); (3, 4); (4, 5)] in
    assert_iter_count (fact 3) (mk_iter ());
    assert_no_dups (mk_iter ());
    assert_order_preserved (mk_iter ())


let test_linord_iter_next_level2 _ =
    let height = 2 in
    let rec count_linearizations level level_cnt =
        if level > height
        then fact level_cnt
        else (fact level_cnt) * (count_linearizations (1 + level) (2 * level_cnt))
    in
    let expected_count = count_linearizations 1 1 in
    let mk_iter _ =
        let n, prec = mk_binary_level_poset height in
        let pr (a, b) = sprintf "(%d, %d)" a b in
        Debug.trace Trc.pos
            (fun _ -> sprintf "n = %d, ord = [%s]\n" n (str_join ", " (List.map pr prec)));
        linord_iter_first n prec
    in
    assert_iter_count expected_count (mk_iter ());
    assert_no_dups (mk_iter ());
    assert_order_preserved (mk_iter ())


let test_linord_iter_next_random _ =
    Random.init 12012016; (* fix the seed *)
    let n = 6 in
    let gen_deps _ =
        BatList.filter
            (fun (i, j) -> i < j && Random.bool ())
            (BatList.cartesian_product (Accums.range 0 n) (Accums.range 0 n))
    in
    for i = 0 to 20 do
        let deps = gen_deps () in
        let mk_iter _ = linord_iter_first n deps in
        assert_order_preserved (mk_iter ());
        assert_no_dups (mk_iter ())
    done


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
        "test_linord_iter_next3" >:: test_linord_iter_next3;
        "test_linord_iter_next4x4" >:: test_linord_iter_next4x4;
        "test_linord_iter_next4x6" >:: test_linord_iter_next4x6;
        "test_linord_iter_next4x2" >:: test_linord_iter_next4x2;
        "test_linord_iter_next7" >:: test_linord_iter_next7;
        "test_linord_iter_next6" >:: test_linord_iter_next6;

        "test_linord_iter_next_3_dots" >:: test_linord_iter_next_3_dots;
        "test_linord_iter_next_4_dots" >:: test_linord_iter_next_4_dots;
        "test_linord_next_broom" >:: test_linord_next_broom;
        "test_linord_iter_next_broom_inverse"
            >:: test_linord_iter_next_broom_inverse;
        "test_linord_iter_next_x_fighter"
            >:: test_linord_iter_next_x_fighter;
        "test_linord_iter_next_pyramide"
            >:: test_linord_iter_next_pyramide;
        "test_linord_iter_next_level2"
            >:: test_linord_iter_next_level2;

        "test_linord_iter_next_5_dots" >:: test_linord_iter_next_5_dots;
        "test_linord_iter_next_10_dots" >:: test_linord_iter_next_8_dots;
        "test_linord_iter_next_3_lines"
            >:: test_linord_iter_next_3_lines;
        "test_linord_iter_next_2_lines_1_dot"
            >:: test_linord_iter_next_2_lines_1_dot;
        "test_linord_iter_next_count_2_lines_2_dots"
            >:: test_linord_iter_next_count_2_lines_2_dots;
        "test_linord_iter_next_2_lines_2_dots"
            >:: test_linord_iter_next_2_lines_2_dots;
        "test_linord_iter_next_2_lines_4_dots"
            >:: test_linord_iter_next_2_lines_4_dots;
        "test_linord_iter_next_1_line_13"
            >:: test_linord_iter_next_1_line_13;
        "test_linord_iter_next_1_line_14"
            >:: test_linord_iter_next_1_line_14;
        "test_linord_iter_next_random"
            >:: test_linord_iter_next_random;
    ]

