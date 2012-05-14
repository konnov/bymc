(* Like batteries, but our own *)

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
    List.fold_left (fun res s -> if res = "" then s else sep ^ s) "" list_of_strings;;
