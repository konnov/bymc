(*
First, "make cuddtop"
Then, type on shour shell the command:
"cuddtop -I installation_path_of_lib" or
"cuddtop" if in source directory, after compilation
*)
#load "cudd.cma"
open Cudd;;

let man = Man.make_d ~numVars:10 ();;
#install_printer Bdd.print__minterm;;
#install_printer Add.print__minterm;;
let x = (Bdd.dnot (Bdd.ithvar man 1));;
let y = (Bdd.dnot (Bdd.ithvar man 2));;
let z = Bdd.ithvar man 3;;
let w = Bdd.ithvar man 4;;

let f = Bdd.dand (Bdd.dand x y) (Bdd.dand (Bdd.dnot z) (Bdd.dnot w));;
let g = Bdd.dand (Bdd.dand y z) (Bdd.dnot w);;
let h = Bdd.dor (Bdd.dor x y) (Bdd.dor z w);;

let r = Bdd.support h;;
let n = Bdd.supportsize h;;

let add1 = Add.ite f (Add.cst man 0.0) (Add.cst man 1.0);;
let supp = Add.support add1;;
let h = Add.guard_of_nonbackground add1;;
Bdd.gendisjdecomp h;;
Add.nbpaths add1;;
Add.nbnonzeropaths add1;;
Add.nbminterms 4 add1;;
Add.nbleaves add1;;
Add.leaves add1;;

let res = Bdd.cube_union f g;;
let res = Bdd.cube_union (Bdd.dnot f) g;;

let f = Bdd.dand (Bdd.dand (Bdd.dnot x) (Bdd.dnot y)) (Bdd.dand z w);;
let g = Bdd.dand (Bdd.dand (Bdd.dnot y) z) w;;

let res = Bdd.support_inter f g;;
let res = Bdd.support_union f g;;
let z = Bdd.nxor x y;;
let z = Bdd.xor x y;;
Bdd.pick_cubes_on_support z (Bdd.cube_of_minterm man [|Man.True;Man.True;Man.True;Man.True|]) 2;;

(* essai des Vdd avec des entiers *)
Gc.set { (Gc.get()) with Gc.verbose = 0x11 };;

let man = Man.make_v ~numVars:20 ();;
#install_printer Bdd.print__minterm;;
let p = Vdd.print__minterm Format.pp_print_int;;
#install_printer p;;

let _ =
  let tab = Array.init 5 (fun i -> Vdd.cst man i) in
  for i=1 to 4 do tab.(i) <- tab.(0) done;
  let res = ref (Bdd.dtrue man) in
  for i=0 to 9 do
    res := Bdd.dand !res (Bdd.xor (Bdd.ithvar man i) (Bdd.ithvar man (i+10)));
  done;
  ()
;;
Man.print_info man;;
Gc.full_major();;
Man.reduce_heap man Man.REORDER_SIFT 1;;
Gc.full_major();;
Man.reduce_heap man Man.REORDER_NONE 0;;
Man.print_info man;;

let x = (Bdd.dnot (Bdd.ithvar man 1));;
let y = (Bdd.dnot (Bdd.ithvar man 2));;
let z = Bdd.ithvar man 3;;
let w = Bdd.ithvar man 4;;

let f = Bdd.dand (Bdd.dand x y) (Bdd.dand (Bdd.dnot z) (Bdd.dnot w));;
let g = Bdd.dand (Bdd.dand y z) (Bdd.dnot w);;

let vdd1 = Vdd.ite f (Vdd.cst man 0) (Vdd.cst man 1);;
let supp = Vdd.support vdd1;;
let h = Vdd.guard_of_nonbackground vdd1;;
Bdd.gendisjdecomp h;;
Vdd.nbpaths vdd1;;
Vdd.nbnonzeropaths vdd1;;
Vdd.nbminterms 4 vdd1;;
Vdd.nbleaves vdd1;;
Vdd.leaves vdd1;;

let res = Bdd.cube_union f g;;
let res = Bdd.cube_union (Bdd.dnot f) g;;

let f = Bdd.dand (Bdd.dand (Bdd.dnot x) (Bdd.dnot y)) (Bdd.dand z w);;
let g = Bdd.dand (Bdd.dand (Bdd.dnot y) z) w;;

let res = Bdd.support_inter f g;;
let res = Bdd.support_union f g;;
let z = Bdd.nxor x y;;
let z = Bdd.xor x y;;
Bdd.pick_cubes_on_support z (Bdd.cube_of_minterm man [|Man.True;Man.True;Man.True;Man.True|]) 2;;

(* essai des Vdd avec des références sur des entiers *)
Gc.set { (Gc.get()) with Gc.verbose = 0x11 };;
let man = Man.make_v ~numVars:20 ();;
#install_printer Bdd.print__minterm;;
let p = Vdd.print__minterm (fun fmt r -> Format.pp_print_int fmt !r);;
#install_printer p;;

let finalise_leaf r = Format.printf "finalizing %i@." !r
let make_leaf n = 
  let res = ref n in
  Gc.finalise finalise_leaf res;
  res
;;
let tab = Array.init 30 (fun i -> (i,i,i,Vdd.cst man (make_leaf i)));;
let tab = Array.map (fun (_,_,_,vdd) -> vdd) tab;;
let res = ref tab.(0);;
for i=0 to 9 do
  res := Vdd.ite (Bdd.ithvar man i) tab.(i) !res
done;;
Gc.compact();;
Man.garbage_collect man;;
for i=0 to 9 do
  res := Vdd.ite (Bdd.ithvar man (i+10)) tab.(i) !res
done;;


let x = (Bdd.dnot (Bdd.ithvar man 1));;
let y = (Bdd.dnot (Bdd.ithvar man 2));;
let z = Bdd.ithvar man 3;;
let w = Bdd.ithvar man 4;;

let f = Bdd.dand (Bdd.dand x y) (Bdd.dand (Bdd.dnot z) (Bdd.dnot w));;
let g = Bdd.dand (Bdd.dand y z) (Bdd.dnot w);;


let leaf0 = ref 0 and leaf1 = ref 1;;
let vdd1 = Vdd.ite f (Vdd.cst man leaf0) (Vdd.cst man leaf1);;
let supp = Vdd.support vdd1;;
let h = Vdd.guard_of_nonbackground vdd1;;
let h = Vdd.guard_of_leaf vdd1 leaf0;;
let h = Vdd.guard_of_leaf vdd1 leaf1;;
let h = Vdd.guard_of_leaf vdd1 (ref 0);;
let h = Vdd.guard_of_leaf vdd1 (ref 1);;
Bdd.gendisjdecomp h;;
Vdd.nbpaths vdd1;;
Vdd.nbnonzeropaths vdd1;;
Vdd.nbminterms 4 vdd1;;
Vdd.nbleaves vdd1;;
Vdd.leaves vdd1;;

let res = Bdd.cube_union f g;;
let res = Bdd.cube_union (Bdd.dnot f) g;;

let f = Bdd.dand (Bdd.dand (Bdd.dnot x) (Bdd.dnot y)) (Bdd.dand z w);;
let g = Bdd.dand (Bdd.dand (Bdd.dnot y) z) w;;

let res = Bdd.support_inter f g;;
let res = Bdd.support_union f g;;
let z = Bdd.nxor x y;;
let z = Bdd.xor x y;;
Bdd.pick_cubes_on_support z (Bdd.cube_of_minterm man [|Man.True;Man.True;Man.True;Man.True|]) 2;;



(* essai des Vdd avec des flottants *)

let p = Vdd.print__minterm Format.pp_print_float;;
#install_printer p;;
let x = (Bdd.dnot (Bdd.ithvar man 1));;
let y = (Bdd.dnot (Bdd.ithvar man 2));;
let z = Bdd.ithvar man 3;;
let w = Bdd.ithvar man 4;;

let f = Bdd.dand (Bdd.dand x y) (Bdd.dand (Bdd.dnot z) (Bdd.dnot w));;
let g = Bdd.dand (Bdd.dand y z) (Bdd.dnot w);;

let vdd1 = Vdd.ite f (Vdd.cst man 0.0) (Vdd.cst man 1.0);;
let supp = Vdd.support vdd1;;
let h = Vdd.guard_of_nonbackground vdd1;;
Bdd.gendisjdecomp h;;
Vdd.nbpaths vdd1;;
Vdd.nbnonzeropaths vdd1;;
Vdd.nbminterms 4 vdd1;;
Vdd.nbleaves vdd1;;
Vdd.leaves vdd1;;

let res = Bdd.cube_union f g;;
let res = Bdd.cube_union (Bdd.dnot f) g;;

let f = Bdd.dand (Bdd.dand (Bdd.dnot x) (Bdd.dnot y)) (Bdd.dand z w);;
let g = Bdd.dand (Bdd.dand (Bdd.dnot y) z) w;;

let res = Bdd.support_inter f g;;
let res = Bdd.support_union f g;;
let z = Bdd.nxor x y;;
let z = Bdd.xor x y;;
Bdd.pick_cubes_on_support z (Bdd.cube_of_minterm man [|Man.True;Man.True;Man.True;Man.True|]) 2;;

let op1 = User.make_op1 (+.);;

(* essai des Add *)

let man = Man.make_d ~numVars:10 ();;
#install_printer Bdd.print__minterm;;
#install_printer Add.print__minterm;;

let var = Array.init 9 (fun i -> Bdd.ithvar man i);;
let cst = Array.init 30 (fun i -> Add.cst man (float_of_int i));;

let f = Array.init 7 (fun i -> Bdd.ite var.(i) var.(i+1) var.(i+2));;

let add1 = Add.ite f.(0) cst.(0) cst.(1);;
let add2 = Add.ite f.(1) cst.(2) cst.(4);;

let adda = Add.add add1 add2;;
type pid = Custom.pid
type memo = Custom.memo =
  | Global
  | Cache of Cache.t
  | Hash of Hash.t
type common = Custom.common = {
  pid: pid;
  arity: int;
  memo: memo;
}

let op1 = Add.make_op1 (fun x -> x +.1.0);;


Add.apply_op1 op1 adda;;
let add = 
  Add.map_op1 (fun x -> x+.1.0) add1
;;
let addb = 
  Add.map_op2 
    ~commutative:true 
    (fun x y -> Gc.compact (); x +. y)  add1 add2
;;

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
testop f Add.mul (Add.map_op2 ~commutative:true (fun x y -> Gc.compact (); x *. y));;
testop g Add.mul (Add.map_op2 ~commutative:true (fun x y -> Gc.compact (); x *. y));;
testop h Add.mul (Add.map_op2 ~commutative:true (fun x y -> Gc.compact (); x *. y));;

(* ********************************************************************** *)

open Cudd;;
let _ = 
  let man = Man.make_v ~numVars:2 () in
(*
  let x = (Bdd.dnot (Bdd.ithvar man 1)) in
  let y = (Bdd.dnot (Bdd.ithvar man 2)) in
*)
  let z = Bdd.ithvar man 0 in
  let w = Bdd.ithvar man 1 in
(*  
  let f = Bdd.dand (Bdd.dand x y) (Bdd.dand (Bdd.dnot z) (Bdd.dnot w)) in
  let g = Bdd.dand (Bdd.dand y z) (Bdd.dnot w) in
*)
  let f = Bdd.dand z w in
  let supp = Bdd.support f in
(*
  let vdd1 = Vdd.ite f (Vdd.cst man 0.0) (Vdd.cst man 1.0) in
  let supp = Vdd.support vdd1 in
*)
  ()
;;
Gc.compact();;

Gc.full_major();;
