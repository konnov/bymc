(** Custom operations for MTBDDs *)

(*  ********************************************************************** *)
(** {3 Types and values} *)
(*  ********************************************************************** *)

type pid = Custom.pid
type common = Custom.common = {
  pid: pid;
  arity: int;
  memo: Memo.t;
}

type ('a,'b) op1 = ('a,'b) Custom.op1 = {
  common1: common;
  closure1: 'a -> 'b;
}

type ('a,'b,'c) op2 = ('a,'b,'c) Custom.op2 = {
  common2: common;
  closure2: 'a -> 'b -> 'c;
  ospecial2: ('a Vdd.t -> 'b Vdd.t -> 'c Vdd.t option) option;
  commutative: bool;
  idempotent: bool;
}

type ('a,'b) test2 = ('a,'b) Custom.test2 = {
  common2t: common;
  closure2t: 'a -> 'b -> bool;
  ospecial2t: ('a Vdd.t -> 'b Vdd.t -> bool option) option;
  symetric: bool;
  reflexive: bool;
}
type ('a,'b,'c,'d) op3 = ('a,'b,'c,'d) Custom.op3 = {
  common3: common;
  closure3: 'a -> 'b -> 'c -> 'd;
  ospecial3: ('a Vdd.t -> 'b Vdd.t -> 'c Vdd.t -> 'd Vdd.t option) option;
}
type ('a,'b) opN = ('a,'b) Custom.opN = {
  commonN: common;
  arityNbdd : int;
  closureN: Bdd.vt array -> 'a Vdd.t array -> 'b Vdd.t option;
}
type ('a,'b) opG = ('a,'b) Custom.opG = {
  commonG: common;
  arityGbdd: int;
  closureG: Bdd.vt array -> 'a Vdd.t array -> 'b Vdd.t option;
  oclosureBeforeRec: (int*bool -> Bdd.vt array -> 'a Vdd.t array -> (Bdd.vt array * 'a Vdd.t array)) option;
  oclosureIte: (int -> 'b Vdd.t -> 'b Vdd.t -> 'b Vdd.t) option;
}
type 'a exist = 'a Custom.exist = {
  commonexist: common;
  combineexist: ('a,'a,'a) op2;
}
type 'a existand = 'a Custom.existand = {
  commonexistand: common;
  combineexistand: ('a,'a,'a) op2;
  bottomexistand: 'a;
}
type ('a,'b) existop1 = ('a,'b) Custom.existop1 = {
  commonexistop1: common;
  combineexistop1: ('b,'b,'b) op2;
  existop1: ('a,'b) op1;
}
type ('a,'b) existandop1 = ('a,'b) Custom.existandop1 = {
  commonexistandop1: common;
  combineexistandop1: ('b,'b,'b) op2;
  existandop1: ('a,'b) op1;
  bottomexistandop1: 'b;
}

(*  ********************************************************************** *)
(** {3 Miscellaneous} *)
(*  ********************************************************************** *)

let newpid = Custom.newpid

let make_common ?memo arity =
  let pid = newpid () in
  let memo = match memo with
    | None -> Memo.Hash(Hash.create arity)
    | Some x ->
	let ok = match x with
	    | Memo.Global -> arity<=2
	    | Memo.Hash x -> (Hash.arity x) = arity
	    | Memo.Cache x -> (Cache.arity x) = arity
	in
	if not ok then
	  raise (Invalid_argument "User.make_common: expected arity is not the same as arity in memo argument")
	;
	x
  in
  { pid; arity; memo }

let clear_common common = Memo.clear common.memo
let clear_op1 op = clear_common op.common1
let clear_op2 op = clear_common op.common2
let clear_op3 op = clear_common op.common3
let clear_opN op = clear_common op.commonN
let clear_opG op = clear_common op.commonG
let clear_test2 op = clear_common op.common2t
let clear_exist op = clear_common op.commonexist
let clear_existand op = clear_common op.commonexistand
let clear_existop1 op = clear_common op.commonexistop1
let clear_existandop1 op = clear_common op.commonexistandop1

(*  ********************************************************************** *)
(** {3 Making operations} *)
(*  ********************************************************************** *)

let make_op1 ?memo op =
  let common = make_common 1 ?memo in
  { common1 = common; closure1=op }

let make_op2
    ?memo
    ?(commutative=false)
    ?(idempotent=false)
    ?special
    op
    =
  let common = make_common 2 ?memo in
  {
    common2=common;
    closure2=op;
    ospecial2=special;
    commutative=commutative;
    idempotent=idempotent;
  }
let make_test2
    ?memo
    ?(symetric=false)
    ?(reflexive=false)
    ?special
    op
    :
    ('a,'b) test2
    =
  let common = make_common 2 ?memo in
  {
    common2t=common;
    closure2t=op;
    ospecial2t=special;
    symetric;
    reflexive;
  }
let make_op3
    ?memo
    ?special
    op
    =
  let common = make_common 3 ?memo in
  {
    common3=common;
    closure3=op;
    ospecial3=special;
  }
let make_opN ?memo arityB arityV op =
  let common = make_common ?memo (arityB+arityV) in
  { commonN=common; arityNbdd=arityB; closureN=op; }
let make_opG ?memo ?beforeRec ?ite arityB arityV op =
  let common = make_common ?memo (arityB+arityV) in
  {
    commonG=common;
    arityGbdd=arityB;
    closureG=op;
    oclosureBeforeRec=beforeRec;
    oclosureIte=ite;
  }
let make_exist ?memo combine =
  let common = make_common 2 ?memo in
  { commonexist=common; combineexist=combine }
let make_existand ?memo ~bottom combine =
  let common = make_common 3 ?memo in
  { commonexistand=common; combineexistand=combine; bottomexistand=bottom }
let make_existop1 ?memo ~op1 combine =
  let common = make_common 2 ?memo in
  { commonexistop1=common; combineexistop1=combine; existop1=op1 }
let make_existandop1 ?memo ~op1 ~bottom combine =
  let common = make_common 3 ?memo in
  { commonexistandop1=common; combineexistandop1=combine; existandop1=op1; bottomexistandop1=bottom }

(*  ********************************************************************** *)
(** {3 Applying operations} *)
(*  ********************************************************************** *)

let apply_op1 = Custom.apply_op1
let apply_op2 = Custom.apply_op2
let apply_op3 = Custom.apply_op3
let apply_opN = Custom.apply_opN
let apply_opG = Custom.apply_opG
let apply_test2 = Custom.apply_test2
let apply_exist op ~supp = Custom._apply_exist op supp
let apply_existand op ~supp = Custom._apply_existand op supp
let apply_existop1 op ~supp = Custom._apply_existop1 op supp
let apply_existandop1 op ~supp = Custom._apply_existandop1 op supp

(*  ********************************************************************** *)
(** {3 Map operations} *)
(*  ********************************************************************** *)

let map_op1 ?memo op d1 =
  let op = make_op1 ?memo op in
  let res = apply_op1 op d1 in
  if memo=None then Memo.clear op.common1.memo;
  res

let map_op2
    ?memo
    ?commutative ?idempotent
    ?special
    op d1 d2
    =
  let op =
    make_op2 ?memo
      ?commutative ?idempotent
      ?special op
  in
  let res = apply_op2 op d1 d2 in
  if memo=None then Memo.clear op.common2.memo;
  res

let map_op3 ?memo ?special op d1 d2 d3
    =
  let op = make_op3 ?memo ?special op in
  let res = apply_op3 op d1 d2 d3 in
  if memo=None then Memo.clear op.common3.memo;
  res

let map_opN ?memo op tbdd tvdd
    =
  let arityB = Array.length tbdd in
  let arityV = Array.length tvdd in
  let op = make_opN ?memo arityB arityV op in
  let res = apply_opN op tbdd tvdd in
  if memo=None then Memo.clear op.commonN.memo;
  res

let map_test2
    ?memo
    ?symetric ?reflexive
    ?special
    op d1 d2
    :
    bool
    =
  let op =
    make_test2 ?memo
      ?symetric ?reflexive
      ?special op
  in
  let res = apply_test2 op d1 d2 in
  if memo=None then Memo.clear op.common2t.memo;
  res
