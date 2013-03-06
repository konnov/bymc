(** Hash tables of weak pointers, parametrized polymorphic version. *)

type 'a compare = 'a Weakke.compare = {
  hash : 'a -> int;
  equal : 'a -> 'a -> bool;
}

type 'a t = {
  compare : 'a compare;
  hashtbl : 'a Weakke.t
}

let create (hash:'a -> int) (equal:'a -> 'a -> bool) n =  {
  compare = {
    hash=(fun x -> (hash x) land max_int);
    equal=equal
  };
  hashtbl = Weakke.create n
}
let clear t = Weakke.clear t.hashtbl
let fold f t init = Weakke.fold f t.hashtbl init
let iter f t = Weakke.iter f t.hashtbl
let count t = Weakke.count t.hashtbl
let add t data = Weakke.Compare.add t.compare t.hashtbl data
let merge t data = Weakke.Compare.merge t.compare t.hashtbl data
let merge_map t data map = Weakke.Compare.merge_map t.compare t.hashtbl data map
let find t data = Weakke.Compare.find t.compare t.hashtbl data
let remove t data = Weakke.Compare.remove t.compare t.hashtbl data
let mem t data = Weakke.Compare.mem t.compare t.hashtbl data
let find_all t data = Weakke.Compare.find_all t.compare t.hashtbl data
let stats t = Weakke.stats t.hashtbl
let print ?first ?sep ?last print_data fmt t =
  Weakke.print
    ?first ?sep ?last print_data fmt t.hashtbl
