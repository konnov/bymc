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

