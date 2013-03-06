(** Lifting operation on leaves to operations on MTBDDs *)

let restrict = ref false

(*  ********************************************************************** *)
(** {3 Internal functions} *)
(*  ********************************************************************** *)
let combineretractive (guard,leaf) res =
  let man = Vdd.manager res in
  Vdd.ite guard (Vdd.cst man leaf) res

let combineexpansive ~default ~merge (guard,leaf) res =
  let man = Vdd.manager res in
  merge (Vdd.ite guard (Vdd.cst man leaf) default) res

(*  ********************************************************************** *)
(** {3 Arity 1} *)
(*  ********************************************************************** *)

let combineleaf1
    ~(default:'c)
    ~(combine : 'b -> 'c -> 'c)
    (f:Bdd.vt -> 'a -> 'b)
    (vdd:'a Vdd.t)
    :
    'c
    =
  let res = ref default in
  let leaves = Vdd.leaves vdd in
  for i=0 to pred (Array.length leaves) do
    let leaf = leaves.(i) in
    let guard = Vdd.guard_of_leaf vdd leaves.(i) in
    let result = f guard leaf in
    res := combine result !res
  done;
  !res

let mapleaf1
    (f:'a -> 'b)
    (vdd:'a Vdd.t)
    :
    'b Vdd.t
    =
  combineleaf1
    ~default:(Vdd._background (Vdd.manager vdd))
    ~combine:combineretractive
    (fun g leaf -> (g, f leaf))
    vdd

let retractivemapleaf1
    ~(default:'b Vdd.t)
    (f:Bdd.vt -> 'a -> Bdd.vt * 'b)
    (vdd:'a Vdd.t)
  :
    'b Vdd.t
  =
  combineleaf1 ~default ~combine:combineretractive
    f vdd

let expansivemapleaf1
    ~(default:'b Vdd.t)
    ~(merge:'b Vdd.t -> 'b Vdd.t -> 'b Vdd.t)
    (f:Bdd.vt -> 'a -> Bdd.vt * 'b)
    (vdd:'a Vdd.t)
  :
    'b Vdd.t
  =
  combineleaf1 ~default ~combine:(combineexpansive ~default ~merge)
    f vdd


(*  ********************************************************************** *)
(** {3 Arity 2} *)
(*  ********************************************************************** *)

let combineleaf2
    ~(default:'d)
    ~(combine : 'c -> 'd -> 'd)
    (f:Bdd.vt -> 'a -> 'b -> 'c)
    (vdd1:'a Vdd.t)
    (vdd2:'b Vdd.t)
    :
    'd
    =
  let res = ref default in
  let leaves1 = Vdd.leaves vdd1 in
  if !restrict then begin
    for i1=0 to pred (Array.length leaves1) do
      let leaf1 = leaves1.(i1) in
      let guard1 = Vdd.guard_of_leaf vdd1 leaf1 in
      let vdd2 = Vdd.restrict vdd2 guard1 in
      let leaves2 = Vdd.leaves vdd2 in
      for i2=0 to pred (Array.length leaves2) do
	let leaf2 = leaves2.(i2) in
	let guard2 = Vdd.guard_of_leaf vdd2 leaf2 in
	let guard = Bdd.dand guard1 guard2 in
	if not (Bdd.is_false guard) then begin
	  let result = f guard leaf1 leaf2 in
	  res := combine result !res
	end
      done
    done
  end
  else begin
    let guardleafs2 = Vdd.guardleafs vdd2 in
    for i1=0 to pred (Array.length leaves1) do
      let leaf1 = leaves1.(i1) in
      let guard1 = Vdd.guard_of_leaf vdd1 leaf1 in
      for i2=0 to pred (Array.length guardleafs2) do
	let (guard2,leaf2) = guardleafs2.(i2) in
	let guard = Bdd.dand guard1 guard2 in
	if not (Bdd.is_false guard) then begin
	  let result = f guard leaf1 leaf2 in
	  res := combine result !res
	end
      done
    done
  end;
  !res

let retractivemapleaf2
    ~(default:'c Vdd.t)
    (f:Bdd.vt -> 'a -> 'b -> Bdd.vt * 'c)
    (vdd1:'a Vdd.t)
    (vdd2:'b Vdd.t)
    :
    'c Vdd.t
    =
  combineleaf2 ~default ~combine:combineretractive
    f vdd1 vdd2

let expansivemapleaf2
    ~(default:'c Vdd.t)
    ~(merge:'c Vdd.t -> 'c Vdd.t -> 'c Vdd.t)
    (f:Bdd.vt -> 'a -> 'b -> Bdd.vt * 'c)
    (vdd1:'a Vdd.t)
    (vdd2:'b Vdd.t)
    :
    'c Vdd.t
    =
  combineleaf2 ~default ~combine:(combineexpansive ~default ~merge)
    f vdd1 vdd2

let mapleaf2
    (f:'a -> 'b -> 'c)
    (vdd1:'a Vdd.t)
    (vdd2:'b Vdd.t)
    :
    'c Vdd.t
    =
  combineleaf2
    ~default:(Vdd._background (Vdd.manager vdd1))
    ~combine:combineretractive
    (fun g leaf1 leaf2 -> (g, f leaf1 leaf2))
    vdd1 vdd2

(*  ********************************************************************** *)
(** {3 Arity 3 or more} *)
(*  ********************************************************************** *)

let combineleaf_array
    ~(default:'c)
    ~(combine : 'b -> 'c -> 'c)
    ~(tabsorbant: ('a -> bool) option array)
    (f:Bdd.vt -> 'a array -> 'b)
    (tvdd:'a Vdd.t array)
    :
    'c
    =
  let length = Array.length tvdd in
  assert(length>=1);
  let cudd = Vdd.manager tvdd.(0) in
  let res = ref default in

  if !restrict then begin
    let rec parcours (guard1,tleaf1) tvdd i1 =
      if tvdd=[||] then
	let nguardleaf = f guard1 tleaf1 in
	res := combine nguardleaf !res
      else
	let vdd2 = tvdd.(0) in
	if Vdd.is_cst vdd2 then
	  let leaf2 = Vdd.dval vdd2 in
	  begin match tabsorbant.(i1) with
	  | Some(f) when f leaf2 -> ()
	  | _ ->
	      let tvdd3 = Array.sub tvdd 1 (length-i1) in
	      parcours (guard1,Array.append tleaf1 [|leaf2|]) tvdd3 (i1+1)
	  end
	else
	  let leaves2 = Vdd.leaves vdd2 in
	  for i2=0 to pred (Array.length leaves2) do
	    let leaf2 = leaves2.(i2) in
	    begin match tabsorbant.(i1) with
	    | Some(f) when f leaf2 -> ()
	    | _ ->
		let guard2 = Vdd.guard_of_leaf vdd2 leaf2 in
		let guard = Bdd.dand guard1 guard2 in
		if not (Bdd.is_false guard) then
		  let tvdd3 =
		    Array.init
		      ((Array.length tvdd) - 1)
		      (fun i -> Vdd.restrict tvdd.(i+1) guard)
		  in
		  parcours (guard,Array.append tleaf1 [|leaf2|]) tvdd3 (i1+1)
	    end
	  done;
    in
    parcours (Bdd.dtrue cudd,[||]) tvdd 0
  end else begin
    let tguardleafs = Array.map Vdd.guardleafs tvdd in
    let rec parcours (guard1,tleaf1) i1 : unit =
      if i1 = length then
	let nguardleaf = f guard1 tleaf1 in
	res := combine nguardleaf !res
      else begin
	let guardleafs2 = tguardleafs.(i1) in
	for i2=0 to pred (Array.length guardleafs2) do
	  let (guard2,leaf2) = guardleafs2.(i2) in
	  begin match tabsorbant.(i1) with
	  | Some(f) when f leaf2 -> ()
	  | _ ->
	      let guard = Bdd.dand guard1 guard2 in
	      if not (Bdd.is_false guard) then
		parcours (guard,Array.append tleaf1 [|leaf2|]) (i1+1)
	  end
	done;
      end
    in
    parcours (Bdd.dtrue cudd,[||]) 0
  end
  ;
  !res

let combineleaf1_array
    ~(default:'d)
    ~(combine : 'c -> 'd -> 'd)
    ?(absorbant:('a -> bool) option)
    ~(tabsorbant: ('b -> bool) option array)
    (f:Bdd.vt -> 'a -> 'b array -> 'c)
    (vdd:'a Vdd.t) (tvdd:'b Vdd.t array)
    :
    'd
    =
  let (absorbant :('b -> bool) option) = Obj.magic absorbant in
  let (vdd : 'b Vdd.t) = Obj.magic vdd in
  let (f : Bdd.vt -> 'b -> 'b array -> 'c) = Obj.magic f in
  combineleaf_array
    ~default
    ~combine
    ~tabsorbant:(Array.append [|absorbant|] tabsorbant)
    (fun guard tleaf ->
      let leaf = tleaf.(0) in
      let tleaf = Array.sub tleaf 1 ((Array.length tleaf)-1) in
      f guard leaf tleaf
    )
    (Array.append [|vdd|] tvdd)

let combineleaf2_array
    ~(default:'e)
    ~(combine : 'd -> 'e -> 'e)
    ?(absorbant1:('a -> bool) option)
    ?(absorbant2:('b -> bool) option)
    ~(tabsorbant: ('c -> bool) option array)
    (f:Bdd.vt -> 'a -> 'b -> 'c array -> 'd)
    (vdd1:'a Vdd.t) (vdd2:'b Vdd.t) (tvdd:'c Vdd.t array)
    :
    'e
    =
  let (absorbant1 :('c -> bool) option) = Obj.magic absorbant1 in
  let (absorbant2 :('c -> bool) option) = Obj.magic absorbant2 in
  let (vdd1 : 'c Vdd.t) = Obj.magic vdd1 in
  let (vdd2 : 'c Vdd.t) = Obj.magic vdd2 in
  let (f : Bdd.vt -> 'c -> 'c -> 'c array -> 'd) = Obj.magic f in
  combineleaf_array
    ~default
    ~combine
    ~tabsorbant:(Array.append [|absorbant1;absorbant2|] tabsorbant)
    (fun guard tleaf ->
      let leaf1 = tleaf.(0) in
      let leaf2 = tleaf.(1) in
      let tleaf = Array.sub tleaf 2 ((Array.length tleaf)-2) in
      f guard leaf1 leaf2 tleaf
    )
    (Array.append [|vdd1;vdd2|] tvdd)
