(*
  Set membership as division by prime numbers.
  This was a clever exercise. However, it is much easier
  (and probably more efficient) to use a bit vector instead of prime
  numbers.
 *)
open Big_int

type elt = big_int
type t = big_int

let before = ref (big_int_of_int 2) (* a number before the next prime *)

(* this is supposed to work with very small prime numbers *)
let new_thing () =
    let rec is_prime num n2 d =
        if ge_big_int d n2
        then true
        else if eq_big_int (mod_big_int num d) zero_big_int
            then false
            else is_prime num n2 (succ_big_int d)
    in
    let rec search num =
        let n2 = succ_big_int (div_big_int num (big_int_of_int 2)) in
        if is_prime num n2 (big_int_of_int 2)
        then num
        else search (succ_big_int num)
    in
    let new_prime = search (!before) in
    before := succ_big_int new_prime;
    new_prime

let str = string_of_big_int

let elem_str = string_of_big_int

let elem_eq a b = eq_big_int a b

let empty = unit_big_int (* it corresponds to an empty set *)

let singleton e = e

let is_empty s = (0 = (compare_big_int s empty))

let mem e set =
    eq_big_int (mod_big_int set e) zero_big_int

let add e set =
    if mem e set
    then set 
    else mult_big_int set e

let remove e set =
    if mem e set
    then div_big_int set e
    else set

let compare = compare_big_int

let compare_elt = compare_big_int

let inter s1 s2 = gcd_big_int s1 s2

let union s1 s2 = mult_big_int s1 s2

let diff s1 s2 = div_big_int s1 (gcd_big_int s1 s2)

let equal s1 s2 =
    0 = (compare_big_int s1 s2)

let subseteq smaller larger =
    eq_big_int zero_big_int (mod_big_int larger smaller)

