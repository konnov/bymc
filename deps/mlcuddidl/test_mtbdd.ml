open Format;;
open Cudd;;

let print_value fmt v = pp_print_int fmt (Obj.magic v);;

let mand = Man.make_d ();;
Man.set_background mand (-.1000000000.0);;
let manv = Man.make_v ();;
Gc.set { (Gc.get()) with Gc.verbose = 0x11 };;
Man.set_gc 1000000 (fun () -> Gc.major(); printf "@.CUDD GARBAGE@.")(fun () -> Gc.major(); printf "@.CUDD  REORDERING@.");;
Man.print_limit := 30;;


Man.enable_autodyn mand Man.REORDER_SIFT;;
Man.enable_autodyn manv Man.REORDER_SIFT;;
Man.set_next_autodyn mand 1000;;
Man.set_next_autodyn manv 1000;;

module F = struct
  type leaf = float
  let pp_print_leaf = pp_print_float

  type t = leaf Mtbddc.t

  let (table:leaf Mtbddc.table) =
    Mtbddc.make_table ~hash:Hashtbl.hash ~equal:(=)

  let get = Mtbddc.get
  let unique = Mtbddc.unique
  let ite = Mtbddc.ite
  let restrict = Mtbddc.restrict
  let tdrestrict = Mtbddc.tdrestrict
  let print = Mtbddc.print_minterm pp_print_int pp_print_leaf

  let cst dbl = Mtbddc.cst manv table dbl

  let is_zero dd =
    if Mtbddc.is_cst dd then
      (Mtbddc.dval dd)=0.0
    else
      false
  let is_one dd =
    if Mtbddc.is_cst dd then
      (Mtbddc.dval dd)=1.0
    else
      false

  let is_leq dd1 dd2 =
    User.map_test2 ~reflexive:true
      (fun xu yu -> (get xu)<=(get yu))
      dd1 dd2

  let negate dd =
    User.map_op1
      (fun xu -> unique table (-. (get xu)))
      dd

  let add dd1 dd2 =
    User.map_op2 ~commutative:true
      ~special:(fun dd1 dd2 ->
	if is_zero dd1 then Some dd2
	else if is_zero dd2 then Some dd1
	else None
      )
      (fun xu yu -> unique table ((get xu) +.(get yu)))
      dd1 dd2

  let mul dd1 dd2 =
    User.map_op2 ~commutative:true
      ~special:(fun dd1 dd2 ->
	if is_zero dd1 then Some dd1
	else if is_zero dd2 then Some dd2
	else if is_one dd1 then Some dd2
	else if is_one dd2 then Some dd1
	else None
      )
      (fun xu yu -> unique table ((get xu) *.(get yu)))
      dd1 dd2
end;;

let print_table () =
  if false then
    printf "table=%a@."
      (PWeakke.print 
	(fun fmt l -> fprintf fmt "(%f,%a)" (Obj.magic l) print_value l))
      F.table
;;


module R = struct
  include Add
  let cst = cst mand
  let ite bddv r1 r2 =
    let bddd = Bdd.transfer bddv mand in
    ite bddd r1 r2

  let restrict f bddv = restrict f (Bdd.transfer bddv mand)
  let tdrestrict f bddv = tdrestrict f (Bdd.transfer bddv mand)

  let print = Add.print_minterm pp_print_int pp_print_float
end;;

let rec equal dd1 add2 =
  let res = 
    if Mtbddc.is_cst dd1 && Add.is_cst add2 then
      (Mtbddc.dval dd1)=(Add.dval add2)
    else if not (Mtbddc.is_cst dd1) && not (Add.is_cst add2) then
      let top1 = Mtbddc.topvar dd1 in
      let then1 = Mtbddc.dthen dd1 in
      let else1 = Mtbddc.delse dd1 in
      let (then2,else2) = Add.cofactors top1 add2 in
      equal then1 then2 && equal else1 else2
    else
      false
  in
  if not res then begin
    printf "@.PROBLEM EQUAL:@.(@[<hv>%a,@ %a@])@."
      F.print dd1 R.print add2
    ;
    failwith "";
  end;
  res
;;

type t = { f: F.t; r: R.t };;
let check t =
  if equal t.f t.r then t
  else begin
    printf "@.PROBLEM CHECK:@.(@[<hv>%a,@ %a@])@."
      F.print t.f R.print t.r
    ;
    assert false;
  end
;;
let make f r = check {f=f; r=r};;

module C = struct

  let print fmt t = fprintf fmt "(@[<hv>%a,@ %a@])"
    F.print t.f R.print t.r

  let cst dbl = make (F.cst dbl) (R.cst dbl)

  let ite bddv t1 t2 =
    make
      (F.ite bddv t1.f t2.f)
      (R.ite bddv t1.r t2.r)

  let restrict t bddv = 
     make
      (F.restrict t.f bddv)
      (R.restrict t.r bddv)

  let tdrestrict t bddv = 
     make
      (F.tdrestrict t.f bddv)
      (R.tdrestrict t.r bddv)

  let is_leq t1 t2 =
    let f = F.is_leq t1.f t2.f in
    let r = R.is_leq t1.r t2.r in
    assert(f=r);
    f

  let negate t =
    let f = F.negate t.f in
    let r = R.sub (R.cst 0.0) t.r in
    make f r

  let add t1 t2 =
    let f = F.add t1.f t2.f in
    let r = R.add t1.r t2.r in
    make f r

  let mul t1 t2 =
    let f = F.mul t1.f t2.f in
    let r = R.mul t1.r t2.r in
    make f r
end;;


let rec generate_bdd maxvar depth =
  if depth<=0 then
    (if Random.bool () then Bdd.dtrue else Bdd.dfalse) manv
  else
    let var = Random.int maxvar in
    let var = Bdd.ithvar manv var in
    let var = if Random.bool () then var else Bdd.dnot var in
    if depth=1 then var
    else
      let res = generate_bdd maxvar (depth-1) in
      (if Random.bool () then Bdd.dand else Bdd.dor) var res


let rec generate_t maxvar depth0 maxcst depth =
  if depth<=0 then begin
    let cst = (Random.int (2*maxcst)) - maxcst in
    C.cst (float_of_int cst)
  end
  else begin
    let t1 = generate_t maxvar depth0 maxcst (depth-1) in
    let t2 = generate_t maxvar depth0 maxcst (depth-1) in
    let cond = generate_bdd maxvar depth0 in
    C.ite cond t1 t2
  end
;;

Random.init 2;;
let tr = ref (C.cst 0.0);;
for i=0 to 50 do
  printf "i=%i@." i;

  let t1 = generate_t 15 6 100 4 in
  let t2 = generate_t 15 6 100 4 in
  let bdd = ref (Bdd.dfalse manv) in
  while (Bdd.is_false !bdd) do
    bdd := generate_bdd 15 6;
  done;
  Cudd.Man.garbage_collect manv;
  Cudd.Man.garbage_collect mand;
  
(*
  let t1 = generate_t 15 6 100 4 in
  let t2 = generate_t 3 2 10 2 in
  let bdd = ref (Bdd.dfalse manv) in
  while (Bdd.is_false !bdd) do
    bdd := generate_bdd 15 6;
  done;
*)
  printf "t1=%a@." C.print t1;
  printf "t2=%a@." C.print t2;
  printf "bdd=%a@." Bdd.print__minterm !bdd;
  print_table();
  let t3 = C.add t1 t1 in
  printf "t3=%a@." C.print t3;
  let t4 = C.add t1 t2 in
  printf "t4=%a@." C.print t4;
  let t5 = C.mul t3 t4 in
  printf "t5=%a@." C.print t5;
  let t6 = C.mul t3 t5 in
  printf "t6=%a@." C.print t6;
(* For restrict, the operation is order dependant,so
   it is normal not to have equality 
  let t3 = C.restrict t3 !bdd in
  printf "t3=%a@." C.print t3;
  let t4 = C.restrict t4 !bdd in
  printf "t4=%a@." C.print t4;
  let t5 = C.tdrestrict t5 !bdd in
  printf "t5=%a@." C.print t5;
  let t6 = C.tdrestrict t6 !bdd in
  printf "t6=%a@." C.print t6;
*)
  assert(not (Man.debugcheck manv));
  assert(not (Man.debugcheck mand));
  Man.check_keys manv;
  Man.check_keys mand;
  ()
done
;;


(*
#install_printer Bdd.print__minterm;;
#install_printer R.print;;
#install_printer F.print;;
#install_printer C.print;;
*)
Gc.set { (Gc.get()) with Gc.verbose = 0x13 };;
let b = Array.init 4 (fun i -> Bdd.ithvar manv i);;
let f = Array.init 4 (fun i -> F.cst (float_of_int i));;
let r = Array.init 4 (fun i -> Add.cst mand (float_of_int i));;

let g1 = Bdd.dand (Bdd.dand b.(0) b.(1)) (Bdd.dnot b.(2));;
let g = Bdd.dand (Bdd.dand b.(0) b.(1)) (Bdd.dand (Bdd.dnot b.(2)) (Bdd.dnot b.(3)));;
let h = Bdd.dand (Bdd.dand b.(1) b.(2)) (Bdd.dnot b.(3));;


let t1 = C.ite g (C.cst 2.0) (C.cst 3.0);;
printf "t1=%a@." C.print t1;;
print_table();;
Gc.compact();;
printf "t1=%a@." C.print t1;;
print_table();;
let t = C.add t1 t1;;
printf "t1=%a@." C.print t1;;
printf "t=%a@." C.print t;;
let t = C.mul t t1;;
