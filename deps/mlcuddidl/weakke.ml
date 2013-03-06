(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Damien Doligez, projet Para, INRIA Rocquencourt          *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* $Id: weak.ml,v 1.17 2008/02/29 14:21:22 doligez Exp $ *)
(* Modified by Bertrand Jeannet, provides only weak hashtables *)

type 'a hashtbl = {
  mutable table : 'a Weak.t array;
  mutable hashes : int array array;
  mutable limit : int;               (* bucket size limit *)
  mutable oversize : int;            (* number of oversize buckets *)
  mutable rover : int;               (* for internal bookkeeping *)
};;
type 'a t = 'a hashtbl

type 'a compare = {
  hash : 'a -> int;
  equal : 'a -> 'a -> bool;
}

let get_index t h = (h land max_int) mod (Array.length t.table);;

let limit = 7;;
let over_limit = 2;;

let create sz =
  let emptybucket = Weak.create 0 in
  let sz = if sz < 7 then 7 else sz in
  let sz = if sz > Sys.max_array_length then Sys.max_array_length else sz in
  {
    table = Array.create sz emptybucket;
    hashes = Array.create sz [| |];
    limit = limit;
    oversize = 0;
    rover = 0;
  };;

let clear t =
  let emptybucket = Weak.create 0 in
  for i = 0 to Array.length t.table - 1 do
    t.table.(i) <- emptybucket;
    t.hashes.(i) <- [| |];
  done;
  t.limit <- limit;
  t.oversize <- 0;
;;

let fold f t init =
  let rec fold_bucket i b accu =
    if i >= Weak.length b then accu else
      match Weak.get b i with
      | Some v -> fold_bucket (i+1) b (f v accu)
      | None -> fold_bucket (i+1) b accu
  in
  Array.fold_right (fold_bucket 0) t.table init
;;

let iter f t =
  let rec iter_bucket i b =
    if i >= Weak.length b then () else
      match Weak.get b i with
      | Some v -> f v; iter_bucket (i+1) b
      | None -> iter_bucket (i+1) b
  in
  Array.iter (iter_bucket 0) t.table
;;

let iter_weak f t =
  let rec iter_bucket i j b =
    if i >= Weak.length b then () else
      match Weak.check b i with
      | true -> f b t.hashes.(j) i; iter_bucket (i+1) j b
      | false -> iter_bucket (i+1) j b
  in
  Array.iteri (iter_bucket 0) t.table
;;

let rec count_bucket i b accu =
  if i >= Weak.length b then accu else
    count_bucket (i+1) b (accu + (if Weak.check b i then 1 else 0))
;;

let count t =
  Array.fold_right (count_bucket 0) t.table 0
;;

let next_sz n = min (3 * n / 2 + 3) Sys.max_array_length;;
let prev_sz n = ((n - 3) * 2 + 2) / 3;;

let test_shrink_bucket t =
  let bucket = t.table.(t.rover) in
  let hbucket = t.hashes.(t.rover) in
  let len = Weak.length bucket in
  let prev_len = prev_sz len in
  let live = count_bucket 0 bucket 0 in
  if live <= prev_len then begin
    let rec loop i j =
      if j >= prev_len then begin
	if Weak.check bucket i then loop (i + 1) j
	else if Weak.check bucket j then begin
	  Weak.blit bucket j bucket i 1;
	  hbucket.(i) <- hbucket.(j);
	  loop (i + 1) (j - 1);
	end else loop i (j - 1);
      end;
    in
    loop 0 (Weak.length bucket - 1);
    if prev_len = 0 then begin
      let emptybucket = Weak.create 0 in
      t.table.(t.rover) <- emptybucket;
      t.hashes.(t.rover) <- [| |];
    end else begin
      Obj.truncate (Obj.repr bucket) (prev_len + 1);
      Obj.truncate (Obj.repr hbucket) prev_len;
    end;
    if len > t.limit && prev_len <= t.limit then t.oversize <- t.oversize - 1;
  end;
  t.rover <- (t.rover + 1) mod (Array.length t.table);
;;

let rec resize t =
  let oldlen = Array.length t.table in
  let newlen = next_sz oldlen in
  if newlen > oldlen then begin
    let newt = create newlen in
    let add_weak ob oh oi =
      let setter nb ni _ = Weak.blit ob oi nb ni 1 in
      let h = oh.(oi) in
      add_aux newt setter None h (get_index newt h);
    in
    iter_weak add_weak t;
    t.table <- newt.table;
    t.hashes <- newt.hashes;
    t.limit <- newt.limit;
    t.oversize <- newt.oversize;
    t.rover <- t.rover mod Array.length newt.table;
  end else begin
    t.limit <- max_int;             (* maximum size already reached *)
    t.oversize <- 0;
  end

and add_aux t setter d h index =
  let bucket = t.table.(index) in
  let hashes = t.hashes.(index) in
  let sz = Weak.length bucket in
  let rec loop i =
    if i >= sz then begin
      let newsz = min (3 * sz / 2 + 3) (Sys.max_array_length - 1) in
      if newsz <= sz then failwith "Weak.Make: hash bucket cannot grow more";
      let newbucket = Weak.create newsz in
      let newhashes = Array.make newsz 0 in
      Weak.blit bucket 0 newbucket 0 sz;
      Array.blit hashes 0 newhashes 0 sz;
      setter newbucket sz d;
      newhashes.(sz) <- h;
      t.table.(index) <- newbucket;
      t.hashes.(index) <- newhashes;
      if sz <= t.limit && newsz > t.limit then begin
	t.oversize <- t.oversize + 1;
	for i = 0 to over_limit do test_shrink_bucket t done;
      end;
      if t.oversize > Array.length t.table / over_limit then resize t;
    end else if Weak.check bucket i then begin
      loop (i + 1)
    end else begin
      setter bucket i d;
      hashes.(i) <- h;
    end;
  in
  loop 0;
;;

let stats t =
  let len = Array.length t.table in
  let lens = Array.map Weak.length t.table in
  Array.sort compare lens;
  let totlen = Array.fold_left ( + ) 0 lens in
  (len, count t, totlen, lens.(0), lens.(len/2), lens.(len-1))
;;

let print
    ?(first : (unit, Format.formatter, unit) format = ("[@[<hv>" : (unit, Format.formatter, unit) format))
    ?(sep : (unit, Format.formatter, unit) format = (";@ ":(unit, Format.formatter, unit) format))
    ?(last : (unit, Format.formatter, unit) format = ("@]]":(unit, Format.formatter, unit) format))
    (print_data:Format.formatter -> 'a -> unit)
    (formatter:Format.formatter)
    (hash:'a hashtbl)
    : unit
    =
  Format.fprintf formatter first;
  let firstitem = ref true in
  iter
    (begin fun data ->
      if !firstitem then firstitem := false else Format.fprintf formatter sep;
      print_data formatter data;
    end)
    hash;
  Format.fprintf formatter last

module Compare = struct
  let add compare t d =
    let h = compare.hash d in
    add_aux t Weak.set (Some d) h (get_index t h);
  ;;

  let find_or compare t d ifnotfound =
    let h = compare.hash d in
    let index = get_index t h in
    let bucket = t.table.(index) in
    let hashes = t.hashes.(index) in
    let sz = Weak.length bucket in
    let rec loop i =
      if i >= sz then ifnotfound h index
      else if h = hashes.(i) then begin
	match Weak.get_copy bucket i with
	| Some v when compare.equal v d
	   -> begin match Weak.get bucket i with
	      | Some v -> v
	      | None -> loop (i + 1)
	      end
	| _ -> loop (i + 1)
      end else loop (i + 1)
    in
    loop 0
  ;;

  let merge compare t d =
    find_or compare t d (fun h index -> add_aux t Weak.set (Some d) h index; d)
  ;;

  let merge_map compare t d map =
    find_or compare t d (fun h index ->
      let d = map d in
      add_aux t Weak.set (Some d) h index; d)
  ;;

  let find compare t d = find_or compare t d (fun h index -> raise Not_found);;

  let find_shadow compare t d iffound ifnotfound =
    let h = compare.hash d in
    let index = get_index t h in
    let bucket = t.table.(index) in
    let hashes = t.hashes.(index) in
    let sz = Weak.length bucket in
    let rec loop i =
      if i >= sz then ifnotfound
      else if h = hashes.(i) then begin
	match Weak.get_copy bucket i with
	| Some v when compare.equal v d -> iffound bucket i
	| _ -> loop (i + 1)
      end else loop (i + 1)
    in
    loop 0
  ;;

  let remove compare t d = find_shadow compare t d (fun w i -> Weak.set w i None) ();;

  let mem compare t d = find_shadow compare t d (fun w i -> true) false;;

  let find_all compare t d =
    let h = compare.hash d in
    let index = get_index t h in
    let bucket = t.table.(index) in
    let hashes = t.hashes.(index) in
    let sz = Weak.length bucket in
    let rec loop i accu =
      if i >= sz then accu
      else if h = hashes.(i) then begin
	match Weak.get_copy bucket i with
	| Some v when compare.equal v d
	   -> begin match Weak.get bucket i with
	      | Some v -> loop (i + 1) (v :: accu)
	      | None -> loop (i + 1) accu
	      end
	| _ -> loop (i + 1) accu
      end else loop (i + 1) accu
    in
    loop 0 []
  ;;
end

(** Weak hash tables *)

module type S = sig
  type data
  type t
  val create : int -> t
  val clear : t -> unit
  val merge : t -> data -> data
  val merge_map : t -> data -> (data -> data) -> data
  val add : t -> data -> unit
  val remove : t -> data -> unit
  val find : t -> data -> data
  val find_all : t -> data -> data list
  val mem : t -> data -> bool
  val iter : (data -> unit) -> t -> unit
  val fold : (data -> 'a -> 'a) -> t -> 'a -> 'a
  val count : t -> int
  val stats : t -> int * int * int * int * int * int
  val print :
    ?first:(unit, Format.formatter, unit) format ->
    ?sep:(unit, Format.formatter, unit) format ->
    ?last:(unit, Format.formatter, unit) format ->
    (Format.formatter -> data -> unit) ->
    Format.formatter -> t -> unit
end

module Make (H : Hashtbl.HashedType) : (S with type data = H.t
					  and type t = H.t hashtbl) =
struct
  type data = H.t
  type t = H.t hashtbl

  let compare = { hash = H.hash; equal = H.equal }

  let create = create
  let clear = clear
  let fold = fold
  let iter = iter
  let count = count
  let add = Compare.add compare
  let merge = Compare.merge compare
  let merge_map = Compare.merge_map compare
  let find = Compare.find compare
  let remove = Compare.remove compare
  let mem = Compare.mem compare
  let find_all = Compare.find_all compare
  let stats = stats
  let print = print
end

let compare = {
  hash=Hashtbl.hash;
  equal=(=)
}

let add t data = Compare.add compare t data
let merge t data = Compare.merge compare t data
let merge_map t data map = Compare.merge_map compare t data map
let find t data = Compare.find compare t data
let remove t data = Compare.remove compare t data
let mem t data = Compare.mem compare t data
let find_all t data = Compare.find_all compare t data
