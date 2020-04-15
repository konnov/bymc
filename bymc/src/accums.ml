(**
   Utility functions that do not fit elsewhere.
   Many of these functions can be replaced by ocaml batteries.
   Since we are using ocaml batteries, we should get rid of many of these.

   Igor Konnov, 2011-2016
*)

open Printf
open Str

exception Not_found_msg of string

module IntSet = BatSet.Make (struct
 type t = int
 let compare a b = a - b
end)

module IntMap = BatMap.Make (struct
 type t = int
 let compare a b = a - b
end)

module StringMap = BatMap.Make(String) (* deprecated: use StrMap *)
module StrMap = BatMap.Make(String)
module StrSet = BatSet.Make(String)

(** a shorter name for string_of_int *)
let int_s i = string_of_int i
(** a shorter name for int_of_string *)
let str_i s = int_of_string s


(** make a cartesian product of lst on itself n times *)
let rec mk_product lst n =
    if n <= 0
    then raise (Failure "mk_product: n must be positive")
    else
        if n = 1
        then List.map (fun e -> [e]) lst
        else List.concat
            (List.map (fun tuple -> List.map (fun e -> e :: tuple) lst)
                (mk_product lst (n - 1)))


(** make a cartesian product of several lists *)
let rec mk_product_of_lists range_lists =
    match range_lists with
    | [] -> raise (Failure "mk_product_of_lists: range_lists is empty")
    | [lst] -> List.map (fun e -> [e]) lst
    | lst :: tail ->
        let cons tuple e = e :: tuple in
        let mult tuple = List.map (cons tuple) lst in
        List.concat (List.map mult (mk_product_of_lists tail))


(** like String.join in python *)
let str_join (sep: string) (strs: string list) =
    let join accum s = if accum <> "" then (accum ^ sep ^ s) else s in
    List.fold_left join "" strs

let str_nempty (s: string): bool = s <> ""

(** create a text representation of StringMap *)
let str_map_s elem_fun map =
    let f k v a =
        Printf.sprintf "%s=%s%s"
            k (elem_fun v) (if a <> "" then ", " ^ a else "")
    in
    StringMap.fold f map ""


(** create a map out of a list of pairs *)
let str_map_of_pair_list (init_map: 'b StrMap.t) (pairs: (string * int) list) =
    let add m (k, v) = StrMap.add k v m in
    List.fold_left add init_map pairs


(** the last element of the list *)    
let rec list_end = function
    | [] -> raise (Invalid_argument "list_end []")
    | [ e ] -> e
    | _ :: tl -> list_end tl

(** split a list into three parts:
    before a matching element, the matching element, the tail.
    If the element is not found, then the two last resulting lists are empty.
 *)
let list_cut_general ignore_dups match_fun lst =
    List.fold_left
        (fun (hl, el, tl) e ->
            match (hl, el, tl) with
            | (_, [some], _) ->
                if not (match_fun e) || ignore_dups
                then (hl, el, tl @ [e])
                else raise (Failure
                    "list_cut found several matching elements")
            | (_, [], []) ->
                if match_fun e
                then (hl, [e], tl)
                else (hl @ [e], [], tl)
            | _ -> raise
                (Failure "Logic error: impossible combination of arguments")
        ) ([], [], []) lst


let list_cut match_fun lst = list_cut_general false match_fun lst

let list_div match_fun lst =
    let hl, el, tl = list_cut_general true match_fun lst in
    (hl, el @ tl)


let list_cut_ignore match_fun lst = list_cut_general true match_fun lst


(** Find the n-th element and
   return the elements before it, the element itself, and the elements after
 *)
let rec list_nth_slice lst n =
    if lst = []
    then raise (Not_found_msg
        (Printf.sprintf "list_nth_split: lst = [], n = %d" n));
    if n < 0 then raise (Not_found_msg "list_nth_split: n < 0");
    match n with
    | 0 -> ([], List.hd lst, List.tl lst)
    | _ ->
        let (h, e, t) = list_nth_slice (List.tl lst) (n - 1) in
        ((List.hd lst) :: h, e, t)


let rec list_sub ilst istart ilen =
    let rec search lst start len =
    match lst with
    | [] ->
        if start <> 0 || len <> 0
        then let m =
            Printf.sprintf
                "list_sub: len(lst) = %d while start = %d and len = %d"
                (List.length ilst) istart ilen in
            raise (Failure m)
        else []
    | hd :: tl ->
        if start > 0
        then list_sub tl (start - 1) len
        else if len > 0
        then hd :: (list_sub tl 0 (len - 1))
        else []
    in
    search ilst istart ilen


(** sort and remove duplicates, one could have used BatList.sort_unique *)
let list_sort_uniq comp_fun lst =    
    let consume_copy l cur prev =
        if (comp_fun cur prev) <> 0 then cur :: l else l in
    let no_dups =
        match List.stable_sort comp_fun lst with
        | [] -> []
        | [hd] -> [hd]
        | hd :: tl ->
                let wo_last = (hd :: (List.rev (List.tl (List.rev tl)))) in
                hd :: (List.rev (List.fold_left2 consume_copy [] tl wo_last))
    in
    no_dups


(** Find the position of the first element equal to e *)
let list_find_pos e lst =
    (* FIXME: use a function from ocaml batteries? *)
    let rec fnd i = function
        | [] -> raise Not_found
        | hd :: tl ->
            if hd = e then i else fnd (1 + i) tl
    in
    fnd 0 lst


let list_find_match_pos match_fun lst =
    (* FIXME: use a function from ocaml batteries? *)
    let rec fnd i = function
        | [] -> raise Not_found
        | hd :: tl ->
            if match_fun hd then i else fnd (1 + i) tl
    in
    fnd 0 lst


(** Python-like range. Deprecated: use sequences from ocaml batteries instead. *)
let rec range i j =
    if j <= i then [] else i :: (range (i + 1) j)

(** Python-like rev_range. Deprecated: use sequences from ocaml batteries instead. *)
let rec rev_range i j =
    if j <= i then [] else (j - 1) :: (rev_range i (j - 1))


let lst_enum l = List.combine (range 0 (List.length l)) l


let str_contains str substr =
    let re = Str.regexp_string substr in
    try ((Str.search_forward re str 0) >= 0) with Not_found -> false


let str_starts_with substr str =
    let ssl = String.length substr in
    if (String.length str) < ssl
    then false
    else (String.sub str 0 ssl) = substr


(**
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
                    if (Hashtbl.find r k) <> v then raise Not_found
                ) l
        in
        try
            subset_eq lhs rhs;
            subset_eq rhs lhs;
            true
        with Not_found ->
            false


let hashtbl_vals tbl = Hashtbl.fold (fun _ v s -> v :: s) tbl []


let hashtbl_keys tbl = Hashtbl.fold (fun k _ s -> k :: s) tbl []


let hashtbl_as_list tbl = Hashtbl.fold (fun k v s -> (k, v) :: s) tbl []

let hashtbl_map f tbl = Hashtbl.fold (fun k v s -> (f k v) :: s) tbl []

let hashtbl_inverse (tbl: ('a, 'b) Hashtbl.t) : (('b, 'a) Hashtbl.t) =
    let inv = Hashtbl.create (Hashtbl.length tbl) in
    Hashtbl.iter (fun k v -> Hashtbl.add inv v k) tbl;
    inv


let hashtbl_filter_keys (pred: 'b -> bool) (tbl: ('a, 'b) Hashtbl.t) : ('a list) =
    let filter k v lst = if pred v then k :: lst else lst in
    Hashtbl.fold filter tbl [] 


(** a convenience function to avoid the plain Not_found message and exceptions *)
let hashtbl_find (err_fun: 'a -> string) (tbl: ('a, 'b) Hashtbl.t) (a: 'a): 'b =
    try Hashtbl.find tbl a
    with Not_found -> raise (Failure ("Not_found: " ^ (err_fun a)))


(** an oftenly needed version of hashtbl_find when a key is a string *)
let hashtbl_find_str (tbl: (string, 'b) Hashtbl.t) (a: string): 'b =
    hashtbl_find (fun s -> s) tbl a


let map_merge_fst key aopt bopt =
    match aopt, bopt with
    | _, None -> aopt
    | Some a, Some _ -> aopt
    | None, Some _ -> bopt

(* regular expressions: OCaml limits the number of matched groups
   to 30. Here we provide an implementation that lifts this
   limitation. This implementation does not support nested groups.
 *)

(** split a regex into two regexes:
     the one ending with group 'group' and the one after that group.
 *)
let re_split re_s text start_pos group =
    let rec find i p =
        if i = 0
        then p
        else find (i - 1) ((search_forward (regexp_string "\\)") re_s p) + 2)
    in
    try
        let p = find group 0 in
        let before = string_before re_s p in
        if not (string_partial_match (regexp before) text start_pos)
        then raise (Invalid_argument (sprintf "no partial match of %s to %s" text before))
        else ((before, string_after re_s p), match_end ())
    with Not_found ->
        raise (Invalid_argument (sprintf "group %d of %s not found" group re_s))


(** retrieve group_cnt matching groups, notwithstanding the group
   limit in ocaml (currently, 30)
 *)
let re_all_groups re_s text group_cnt =
    (* this is the de-facto limit on the number of groups in OCaml 3.12.1 *)
    let limit = 30 in
    let groups r n p =
        if string_partial_match (regexp r) text p
        then List.map (fun i -> matched_group i text) (range 1 (n + 1))
        else raise (Invalid_argument (sprintf "no match of %s:%d to %s" text p r))
    in
    if not (string_match (regexp re_s) text 0)
    then raise (Invalid_argument (sprintf "string '%s' does not match '%s'" text re_s))
    else let rec next r n p =
        if n <= limit
        then groups r n p
        else let ((before, after), np) = re_split r text p limit in
            (groups before limit p) @ (next after (n - limit) np)
    in
    next re_s group_cnt 0


(* misc *)
let n_copies n e =
    let rec gen = function
    | 0 -> []
    | i -> e :: (gen (i - 1))
    in
    gen n


let bits_to_fit n =                                                             
    let rec f b m =
        if n <= m
        then b
        else f (b + 1) (2 * m)
    in
    f 1 2


let rec ipow a n =
    if n <= 0
    then 1
    else a * (ipow a (n - 1))


(** make a short version of a string (by taking a prefix) and ensure there is
   no such a string in the table. If no short version can be generated, then
   a unique number is appended to the string.
 *)
let rec str_shorten tbl s =
    let rec append_num i =
        let news = s ^ (string_of_int i) in
        if not (Hashtbl.mem tbl news)
        then news
        else append_num (i + 1)
    in
    let rec gen l sz =
        let sub = String.sub s 0 l in
        if not (Hashtbl.mem tbl sub)
        then sub
        else if (l >= sz) then append_num 0 else gen (l + 1) sz
    in
    gen 1 (String.length s)


let is_none (o: 'a option): bool =
    match o with
    | None -> true
    | Some _ -> false


let get_some (o: 'a option): 'a =
    match o with
    | Some x -> x
    | None -> raise (Failure "The argument is None, expected Some _")


let fold_file line_fun a filename =
    let fin = open_in filename in
    let rec read l =
        try read (line_fun l (input_line fin))
        with End_of_file ->
            close_in fin; l
    in
    read a

(** A stop-watch class to measure time *)
class stop_watch ~(is_wall: bool) ~(with_children: bool) =
    object(self)
        val mutable start_time = 0.0
        val mutable last_time = 0.0
        val mutable last_event = ""
        val mutable last_print_sec = 0.0

        method start event_name =
            start_time <- self#get_time ();
            last_time <- self#get_time ();
            last_event <- "";
            last_print_sec <- 0.0;
            ignore (self#next_event event_name)

        method next_event event_name =
            let current_time = self#get_time () in
            let since_start = current_time -. start_time in
            let lap = current_time -. last_time in
            last_time <- current_time;
            last_event <- event_name;
            (since_start, lap)

        method next_event_and_print event_name =
            let current_time = self#get_time () in
            if last_event <> ""
            then Printf.printf "  %s: %f sec\n"
                last_event (current_time -. last_time);
            last_time <- current_time;
            last_event <- event_name

        (** print only if the given period has elapsed since the last time *)
        method print_once_in_interval interval_sec msg =
            if last_time -. last_print_sec >= interval_sec
            then begin
                last_print_sec <- last_time;
                print_string msg
            end

        method private get_time () =
            if is_wall
            then Unix.time()
            else if with_children
                then let t = Unix.times () in
                    (t.Unix.tms_utime +. t.Unix.tms_stime
                        +. t.Unix.tms_cutime +. t.Unix.tms_cstime)
                else Sys.time()
    end


let days = [| "Sun"; "Mon"; "Tue"; "Wed"; "Thu"; "Fri"; "Sat" |]
let months = [| "Jan"; "Feb"; "Mar"; "Apr"; "May"; "Jun";
                "Jul"; "Aug"; "Sep"; "Oct"; "Nov"; "Dec" |]

 
let format_time time =
  let tm = Unix.localtime time in
  Printf.sprintf "%s %s %2d %02d:%02d:%02d %04d"
    days.(tm.Unix.tm_wday)
    months.(tm.Unix.tm_mon)
    tm.Unix.tm_mday
    tm.Unix.tm_hour
    tm.Unix.tm_min
    tm.Unix.tm_sec
    (tm.Unix.tm_year + 1900)


let format_time_now () = format_time (Unix.time ())

 
let short_time time =
  let tm = Unix.localtime time in
  Printf.sprintf "%02d%02d%02d"
    tm.Unix.tm_hour
    tm.Unix.tm_min
    tm.Unix.tm_sec


let short_time_now () = short_time (Unix.time ())


(**
 A human-readable printer for a duration, which is stripping the
 unnecessary details.
 *)
let human_readable_duration duration =
    let plural s num =
        if num mod 10 = 1 then s else s ^ "s"
    in
    let secs = (int_of_float duration) mod 60 in
    let mins = ((int_of_float duration) / 60) mod 60 in
    let hours = ((int_of_float duration) / 3600) mod 24 in
    let days = (int_of_float duration) / (24 * 3600) in
    if duration < 1.0
    then sprintf "% 1.6f s." duration
    else if duration < 10.0
    then sprintf "% 1.3f s." duration
    else if duration < 60.0
    then sprintf "% 2d s." secs
    else if duration < 3600.0
    then sprintf "% 2d min % 2d s" mins secs
    else if duration < 24. *. 3600.0
    then sprintf "% 2d %s % 2d min" hours (plural "hour" hours) mins
    else sprintf "% 3d %s % 2d %s % 2d min"
        days (plural "day" days) hours (plural "hour" hours) mins

