(*
#load "cudd.cma";;

#install_printer Bdd.print__minterm;;
#install_printer Add.print__minterm;;
*)
open Format;;
open Cudd;;

(*
For interactive session:
type on shour shell the command:
"make cuddtop"
and then
"cuddtop -I installation_path_of_lib" or
"cuddtop" if in source directory, after compilation
*)

let man = Man.make_v ~numVars:10 ();;

(* Identifiers of variables printed as "x", "y,", .... *)
let idx = 0;;
let idy = 1;;
let idz = 2;;
let idw = 3;;

(* Correspondance function *)
let print_id fmt id =
  Format.pp_print_string fmt
    (match id with
    | 0 -> "x"
    | 1 -> "y"
    | 2 -> "z"
    | 3 -> "w"
    | _ as x -> string_of_int x
    )

(* Formula corresponding to litterals "x","y",... *)
let x = Bdd.ithvar man idx;;
let y = Bdd.ithvar man idy;;
let z = Bdd.ithvar man idz;;
let w = Bdd.ithvar man idw;;

(* Raw printing *)
Format.printf "Raw printing:@.x = %a@.y = %a@.z = %a@.w = %a@."
  (Bdd.print_minterm print_id) x
  (Bdd.print_minterm print_id) y
  (Bdd.print_minterm print_id) z
  (Bdd.print_minterm print_id) w
;;
(* Better printing *)
Format.printf "Better printing:@.x = %a@.y = %a@.z = %a@.w = %a@."
  (Bdd.print_minterm print_id) x
  (Bdd.print_minterm print_id) y
  (Bdd.print_minterm print_id) z
  (Bdd.print_minterm print_id) w
;;

let f = Bdd.dand (Bdd.dand x y) (Bdd.dand (Bdd.dnot z) (Bdd.dnot w));;
let g = Bdd.dand (Bdd.dand y z) (Bdd.dnot w);;
(* Raw printing *)
Format.printf "Raw printing:@.f = %a@.g = %a@."
  (Bdd.print_minterm print_id) f
  (Bdd.print_minterm print_id) g
;;
(* Better printing *)
Format.printf "Better printing:@.f = %a@.g = %a@."
  (Bdd.print_minterm print_id) f
  (Bdd.print_minterm print_id) g
;;

(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)

let man = Man.make_d ~numVars:10 ();;

let var = Array.init 9 (fun i -> Bdd.ithvar man i);;
let cst = Array.init 30 (fun i -> Add.cst man (float_of_int i));;

let f = Array.init 7 (fun i -> Bdd.ite var.(i) var.(i+1) var.(i+2));;

(*
Array.iter
  (fun f -> printf "cst = %a@." Add.print__minterm f)
  cst
;;
Array.iter
  (fun f -> printf "f = %a@." Bdd.print__minterm f)
  f
;;
  *)

let add1 = Add.ite f.(0) cst.(0) cst.(1);;
let add2 = Add.ite f.(1) cst.(2) cst.(4);;

(* Addition *)
let adda = Add.add add1 add2;;
let addb = Add.map_op2
  ~memo:(Memo.Cache(Cache.create 3))
  ~idempotent:false
  ~commutative:true
  (fun x y -> Gc.compact (); x +. y)
  add1 add2;;

assert(adda=addb);;

let adda = Add.map_op1 (fun x -> x *. 2.0) adda;;
let addb = Add.map_op1 (fun x -> x *. 2.0) addb;;
assert(adda=addb);;

let opN =
  (begin fun tbdd tadd ->
    let cst = Array.fold_left (fun res add -> res && Add.is_cst add) true tadd in
    if cst then
      let res = Array.fold_left (fun res add -> res +. Add.dval add) 0.0 tadd in
      Some(Add.cst man res)
    else
      None
  end)
let addc =
  Add.map_opN
    opN
    [||] [| add1; add2; add1; add2 |]
;;
assert(adda=addc);;
let addd =
  Add.map_opN
    ~memo:(Memo.Cache(Cache.create 4))
    opN
    [||] [| add1; add2; add1; add2 |]
;;
assert(adda=addd);;

(* Existential quantification (through addition) *)
let op2 = Add.make_op2 ~commutative:true (+.);;
let exist = Add.make_exist op2;;
let supp = Bdd.dand var.(1) var.(2);;
let addc = Add.apply_exist exist ~supp adda;;
Add.clear_op2 op2;;
Add.clear_exist exist;;

let opG = Add.make_opG
  ~ite:(fun index dthen delse ->
    if Bdd.is_var_in index supp
    then Add.apply_op2 op2 dthen delse
    else Add.ite var.(index) dthen delse)
  0 1
  (fun tbdd tadd ->
    if Add.is_cst tadd.(0) then Some(tadd.(0)) else None)
;;
let addd = Add.apply_opG opG [||] [|adda|];;
assert(addc=addd);;
let opG = Add.make_opG
  ~ite:(fun index dthen delse ->
    if Bdd.is_var_in index supp
    then Add.add dthen delse
    else Add.ite var.(index) dthen delse)
  0 1
  (fun tbdd tadd ->
    if Add.is_cst tadd.(0) then Some(tadd.(0)) else None)
;;
let adde = Add.apply_opG opG [||] [|adda|];;
assert(addc=adde);;

(* Existential quantification and operation (through addition) *)
let addc = Add.apply_exist exist ~supp (Add.add adda addb);;
let opG = Add.make_opG
  ~ite:(fun index dthen delse ->
    if Bdd.is_var_in index supp
    then Add.apply_op2 op2 dthen delse
    else Add.ite var.(index) dthen delse)
  0 2
  (fun tbdd tadd ->
    if Add.is_cst tadd.(0) && Add.is_cst tadd.(1)
    then Some(Add.cst man ((Add.dval tadd.(0))+.(Add.dval tadd.(1))))
    else None)
;;
let addd = Add.apply_opG opG [||] [|adda;addb|];;
assert(addc=addd);;





let g = Array.init 6 (fun i -> Bdd.ite var.(i) var.(i+1) (Bdd.dor var.(i+2) var.(i+3)));;
let h = Array.init 6 (fun i -> Bdd.dand f.(i) f.(i+1));;

let make_add bdd index depth =
  let res = ref (Add.ite bdd.(index) cst.(index) cst.(0)) in
  for i=0 to depth-1 do
    res := Add.ite bdd.(index+i) cst.(index+i) !res
  done;
  !res
;;
let testop bdd opa opb =
  for index=0 to (Array.length bdd) - 2 do
    for depth=0 to (Array.length bdd) - index do
      let add1 = make_add bdd index depth in
      let add2 = make_add bdd (index+1) (depth-1) in
      let adda = opa add1 add2 in
      let addb = opb add1 add2 in
      if adda<>addb then failwith "";
    done;
  done;
  ()
;;

testop f Add.add (Add.map_op2 ~commutative:true (+.));;
testop g Add.add (Add.map_op2 ~commutative:true (+.));;
testop h Add.add (Add.map_op2 ~commutative:true (+.));;
testop f Add.mul (Add.map_op2 ~commutative:true (fun x y -> Gc.compact (); ignore (Man.garbage_collect man); x *. y));;
testop g Add.mul (Add.map_op2 ~commutative:true (fun x y -> Gc.compact (); ignore (Man.garbage_collect man); x *. y));;
testop h Add.mul (Add.map_op2 ~commutative:true (fun x y -> Gc.compact (); ignore (Man.garbage_collect man); x *. y));;
