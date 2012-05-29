(* Like batteries, but our own. Useful functions that do not fit elsewhere. *)

(* make a cartesian product of lst on itself n times *)
let rec mk_product lst n =
    if n <= 0
    then raise (Failure "mk_product: n must be positive")
    else
        if n = 1
        then List.map (fun e -> [e]) lst
        else List.concat
            (List.map (fun tuple -> List.map (fun e -> e :: tuple) lst)
                (mk_product lst (n - 1)))
;;

(* like String.join in python *)
let str_join sep list_of_strings =
    List.fold_left
        (fun res s -> if res <> "" then (res ^ sep ^ s) else res ^ s)
        "" list_of_strings
;;

(* separate a list into three parts:
    before a matching element, the matching element, the tail.
    If an element is not found, then two last resulting lists are empty.
 *)
let list_cut match_fun lst =
    List.fold_left
        (fun (hl, el, tl) e ->
            match (hl, el, tl) with
            | (_, [some], _) ->
                if not (match_fun e)
                then (hl, el, tl @ [e])
                else raise (Failure
                    "list_cut found several matching elements")
            | (_, [], []) ->
                if match_fun e
                then (hl, [e], tl)
                else (hl @ [e], [], tl)
            | _ -> raise
                (Failure "Logic error: impossible combination of arguments")
        ) ([], [], []) lst
;;

(* Python-like range *)                                                         
let rec range i j =
    if j <= i then [] else i :: (range (i + 1) j);;

let rec rev_range i j =
    if j <= i then [] else (j - 1) :: (rev_range i (j - 1));;

let str_contains str substr =
    let re = Str.regexp_string substr in
    try ((Str.search_forward re str 0) >= 0) with Not_found -> false;;

(*
   check two hash tables for element equality as standard "=" works
   only on the hash tables of the same capacity!
 *)
let hashtbl_eq lhs rhs =
    if (Hashtbl.length lhs) <> (Hashtbl.length rhs)
    then false
    else
        let subset_eq l r =
            Hashtbl.iter
                (fun k v ->
                    if (Hashtbl.find r k) <> v then raise Not_found)
                l
        in
        try
            subset_eq lhs rhs;
            subset_eq rhs lhs;
            true
        with Not_found ->
            false
;;

let hashtbl_vals tbl = Hashtbl.fold (fun _ v s -> v :: s) tbl [];;

let hashtbl_keys tbl = Hashtbl.fold (fun k _ s -> k :: s) tbl [];;

let bits_to_fit n =                                                             
    let rec f b m =
        if n <= m
        then b
        else f (b + 1) (2 * m)
    in
    f 1 2
;;

