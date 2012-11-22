
type var_role =
    BoundedInt of int * int | SharedUnbounded | LocalUnbounded | Scratch;;

let var_role_s r =
    match r with
    | BoundedInt (a, b) -> Printf.sprintf "bounded[%d, %d]" a b
    | SharedUnbounded -> "shared-unbounded"
    | LocalUnbounded -> "local-unbounded"
    | Scratch -> "scratch"
;;

let is_unbounded = function
    | SharedUnbounded
    | LocalUnbounded -> true
    | _ -> false
;;

let is_bounded = function
    | BoundedInt (_, _) -> true
    | _ -> false
;;

let is_local_unbounded = function
    | LocalUnbounded -> true
    | _ -> false
;;

let is_shared_unbounded = function
    | SharedUnbounded -> true
    | _ -> false
;;

