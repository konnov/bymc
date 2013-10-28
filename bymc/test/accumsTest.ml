open OUnit
open Printf

open Accums

let re = 
    "\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\(a\\)\\(b\\)\\(c\\)\\(d\\)\\(e\\)\\(f\\)\\(g\\)\\(h\\)\\(i\\)\\(j\\)\\(k\\)\\(l\\)\\(m\\)\\(n\\)\\(o\\)\\(p\\)\\(q\\)\\(r\\)\\(s\\)\\(t\\)\\(u\\)\\(v\\)\\(x\\)"


let text = "0123456789abcdefghijklmnopqrstuvx"


let test_re_split5 _ =
    let ((b, a), p) = re_split re text 0 5 in
    assert_equal "\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)" b;
    assert_equal "\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\(a\\)\\(b\\)\\(c\\)\\(d\\)\\(e\\)\\(f\\)\\(g\\)\\(h\\)\\(i\\)\\(j\\)\\(k\\)\\(l\\)\\(m\\)\\(n\\)\\(o\\)\\(p\\)\\(q\\)\\(r\\)\\(s\\)\\(t\\)\\(u\\)\\(v\\)\\(x\\)" a;
    assert_equal 5 p


let test_re_split30 _ =
    let ((b, a), p) = re_split re text 0 30 in
    assert_equal "\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\(a\\)\\(b\\)\\(c\\)\\(d\\)\\(e\\)\\(f\\)\\(g\\)\\(h\\)\\(i\\)\\(j\\)\\(k\\)\\(l\\)\\(m\\)\\(n\\)\\(o\\)\\(p\\)\\(q\\)\\(r\\)\\(s\\)\\(t\\)" b;
    assert_equal "\\(u\\)\\(v\\)\\(x\\)" a;
    assert_equal 30 p


let test_re_split33 _ =
    let ((b, a), p) = re_split re text 0 33 in
    assert_equal "\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\([0-9]\\)\\(a\\)\\(b\\)\\(c\\)\\(d\\)\\(e\\)\\(f\\)\\(g\\)\\(h\\)\\(i\\)\\(j\\)\\(k\\)\\(l\\)\\(m\\)\\(n\\)\\(o\\)\\(p\\)\\(q\\)\\(r\\)\\(s\\)\\(t\\)\\(u\\)\\(v\\)\\(x\\)" b;
    assert_equal "" a;
    assert_equal 33 p


let test_re_split34 _ =
    let f _ = ignore (re_split re text 0 34) in
    assert_raises
        (Invalid_argument (sprintf "group 34 of %s not found" re)) f


let test_re_all_groups _ =
    let groups = re_all_groups re text 33 in
    assert_equal [
        "0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9";
        "a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j";
        "k"; "l"; "m"; "n"; "o"; "p"; "q"; "r"; "s"; "t";
        "u"; "v"; "x"
    ] groups


let suite = "accums-suite" >:::
    [
        "test_re_split5" >:: test_re_split5;
        "test_re_split30" >:: test_re_split30;
        "test_re_split33" >:: test_re_split33;
        "test_re_split34" >:: test_re_split34;
        "test_re_all_groups" >:: test_re_all_groups
    ]

