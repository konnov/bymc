(* Support for encoding of a problem in a SAT solver      *)
(*                                                        *)
(* Igor Konnov, 2011                                      *)

open Map
module StringMap = Map.Make(String)
module StringSet = Set.Make(String)
open Format

(* a SAT formula *)
type form =
    (* a user-defined variable that has a problem-specific name *)
    Var of string
    (* an auxillary variable that does not have a name *)
  | Aux of int
  | Not of form
  | And of form list
  | Or of form list
  | True
  | False

type cnf_layer = { sat_form: form; first_id: int; num_aux_vars: int }


(* a pool of fresh boolean variables *)
class fresh_pool(first_id) =
    object(self)
        val mutable free_id = first_id

        method get_free_id = free_id

        method next_aux =
            let v = Aux(free_id) in
                free_id <- free_id + 1; v
    end


let format_sat_form ff form =
    let rec format_fold f parent =
        match f with
            True -> Format.fprintf ff "1"
          | False -> Format.fprintf ff "0"
          | Var x -> Format.fprintf ff "%s" x
          | Aux i -> Format.fprintf ff "_%d" i
          | Not subform ->
                Format.fprintf ff "~"; format_fold subform '~';

          | And(children) ->
            Format.fprintf ff "%s" (if parent != '&' then "(" else "");
            let first = ref true in
            let print_child subf =
                if subf <> True
                then begin
                    if not !first then Format.fprintf ff ") @,& (";
                    first := false;
                    format_fold subf '&'
                end
            in
            List.iter print_child children;
            Format.fprintf ff "%s" (if parent != '&' then ")" else "");

          | Or(children) ->
            Format.fprintf ff "%s" "(";
            let first = ref true in
            let print_child subf =
                if subf <> False
                then begin
                    if not !first then Format.fprintf ff ") | (";
                    first := false;
                    format_fold subf '|'
                end
            in
            List.iter print_child children;
            Format.fprintf ff "%s" ")";
    in
    format_fold form ' '


(* same but in prefix notation *)
let format_sat_form_polish ff form =
    let rec format_fold = function
        True -> Format.fprintf ff "1@,"
      | False -> Format.fprintf ff "0@,"
      | Var x -> Format.fprintf ff "%s@," x
      | Aux i -> Format.fprintf ff "_%d@," i
      | Not subform ->
            Format.fprintf ff "@,(not ";
            format_fold subform;
            Format.fprintf ff ")@,";

      | And(children) ->
        Format.fprintf ff "@,(and";
        let print_child subf =
            Format.fprintf ff " ";
            if subf <> True then format_fold subf
        in
        List.iter print_child children;
        Format.fprintf ff ")@,";

      | Or(children) ->
        Format.fprintf ff "@,(or";
        let print_child subf =
            Format.fprintf ff " ";
            if subf <> False then format_fold subf
        in
        List.iter print_child children;
        Format.fprintf ff ")@,";
    in
    format_fold form;
    Format.pp_print_flush ff ()


type shape = Literal | Clause | Cnf | Generic


let rec shape_of f =
  match f with
      True    -> Literal
    | False   -> Literal
    | Var x   -> Literal
    | Aux i   -> Literal
    | Not g   -> if (shape_of g) = Literal then Literal else Generic
    | Or children  ->
      if (List.for_all
         (fun g -> let s = (shape_of g) in
            (s = Literal || s == Clause)) children)
      then Clause else Generic;
    | And children ->
      if (List.for_all (fun g -> (shape_of g) != Generic) children)
      then Cnf else Generic


let is_literal f =
  match f with
      Var _ -> true
    | Aux _ -> true
    | Not (Var _) -> true
    | Not (Aux _) -> true
    | f -> false


let isa_clause s = s == Literal || s == Clause

let rec is_clause f =
  match f with
      Var _ -> true
    | Aux _ -> true
    | Not (Var _) -> true
    | Not (Aux _) -> true
    | Or children -> (List.for_all is_clause children)
    | f -> false


let isa_cnf s = s == Literal || s == Clause || s == Cnf

let rec string_of_form f =
  match f with
      True -> "T"
    | False -> "F"
    | Var x -> if x = "" then "<noname>" else x
    | Aux i -> "_" ^ (string_of_int i)
    | Not g -> "~" ^ string_of_form g
    | And children ->
        "("
        ^ (List.fold_left
            (fun s g -> (if s = "" then s else s ^ " & ") ^ (string_of_form g))
            "" children)
        ^ ")"
    | Or children ->
        "("
        ^ (List.fold_left
            (fun s g -> (if s = "" then s else s ^ " | ") ^ (string_of_form g))
            "" children)
        ^ ")"


let rec propagate_not negation g =
    match g with
      True -> if negation then False else g
    | False -> if negation then True else g
    | Var x -> if negation then Not(Var x) else g
    | Aux i -> if negation then Not(Aux i) else g
    | Not Var x -> if negation then Var x else g
    | Not subf -> propagate_not (not negation) subf
    | And children ->
        let new_children = List.rev_map (propagate_not negation) children in
        if negation then Or new_children else And new_children
    | Or children ->
        let new_children = List.rev_map (propagate_not negation) children in
        if negation then And new_children else Or new_children


type level = TOP_AND | TOP_OR | DEEP


let rec tseitin pool level f =
  let absorb_clause lits clause =
    match clause with
      | False        -> lits
      | Var x        -> clause :: lits (* reverse because of using cons *)
      | Aux i        -> clause :: lits (* the same *)
      | Not Var x    -> clause :: lits
      | Not Aux i    -> clause :: lits
      | Or(sub_lits) -> (List.rev_append sub_lits lits)
      | _ -> raise (Invalid_argument ("Neither literal, nor a clause: " ^
                    (string_of_form clause)))
  in
  let or_or_lit lits =
    match lits with
        []  -> True
      | [l] -> l
      | _   -> Or(lits)
  in
  (* the triple (wf_clauses, res_form, idx) is collected through the transformation *)
  match f with
      True    -> ([], True)
    | False   -> ([], False)
    | Var _   -> ([], f)
    | Aux _   -> ([], f)
    | Not Var _ -> ([], f)
    | Not Aux _ -> ([], f)
    | Not _   -> raise (Invalid_argument "Propagate negations first")

    | And children ->
        let mylevel = match level with
            TOP_AND -> TOP_AND
          | _ -> DEEP
        in
        let top_lit = (if level != TOP_AND then pool#next_aux else True)
        in
        let f_cl = (List.fold_left
            (fun wf_cl subf -> (* wf_cl is "well-formed clauses" *)
                (* c_form may equal to True
                   if the result was already propagated to c_cl *)
                let (c_cl, c_form) = tseitin pool mylevel subf in
                if top_lit = True
                (* the top-level clause, just add the formula to the set of clauses *)
                then let cl_tl = (if c_form != True then c_form :: c_cl else c_cl) in
                    (List.rev_append wf_cl cl_tl)
                (* an inner clause, add a binding constraint (top_lit -> c_form) *)
                else let cl_tl =
                    (if c_form != True
                    then Or(absorb_clause [(Not top_lit)] c_form) :: c_cl
                    else c_cl) in
                (List.rev_append wf_cl cl_tl))
            )
            [] children
        in
        (f_cl, top_lit)

    | Or children ->
        let mylevel = match level with
            TOP_AND -> TOP_OR
          | TOP_OR -> DEEP
          | _ -> DEEP
        in
        (* here we do not need to introduce an auxillary variable,
           but propagate the result up after the transformation of children.
           The disjunction will get propagated either to a top-level
           disjunction or it will settle in a condition for an AND-auxillary
           variable. *)
        let (f_cl, f_or_lits) =
            (List.fold_left
            (* wf_cl is "well-formed clauses",
               or_lits are literals collected for the top-level OR,
               i is the last index used *) 
            (fun (wf_cl, or_lits) subf -> (* here we collect the literals into or_lits *)
                (* c_form may be equal to True
                   if the result was already propagated to c_cl *)
                let (c_cl, c_form) = tseitin pool mylevel subf in
                (* just keep collecting literals... *)
                let c_or_lits =
                    (if c_form != True
                     then (absorb_clause or_lits c_form)
                     else or_lits) in
                ((List.rev_append wf_cl c_cl), c_or_lits)
            )
            ([], []) children)
        in
        (* create either a literal or a disjunction *)
        (f_cl, (or_or_lit f_or_lits))


(* Transform a boolean formula to CNF using Tseitin algorithm *)
let cnfify pool f =
  if (shape_of f) = Generic
  then
    let (clauses, _) = (tseitin pool TOP_AND f) in
    And(clauses)
  else f (* the formula is already in CNF *)


(* transform a formula in CNF form to a two-dimensional list of Clauses/Literals *)
let rec cnf_to_lst f =
  let rec collect_single_clause g =
    match g with
      True -> []
    | False ->
            raise (Invalid_argument "Trivially unsatisfiable formula: False is met!")
      | Var _ -> [g]
      | Aux _ -> [g]
      | Not (Var _) -> [g]
      | Not (Aux _) -> [g]
      | Or children ->
            List.fold_left
                (fun cl c -> List.rev_append (collect_single_clause c) cl)
                []
                children
      | g -> raise (Invalid_argument
          ("Unexpected formula: " ^ (string_of_form g)))
  in
  match f with
      And children ->
        List.fold_left
          (fun l c -> List.rev_append (cnf_to_lst c) l)
          []
          children
    | f -> [collect_single_clause f]


(*
 Replace placeholders {-1} and {0} by [src] and [dst] resp.
 for given src and dst.
 
 TODO: generalize?
 TODO: shift auxillary variables
 *)
let rec replace_placeholders f src dst =
    match f with
      True    -> True
    | False   -> False
    | Var x   ->
        let new_name =
            (Str.global_replace
                (Str.regexp_string "{-1}") 
                ("[" ^ (string_of_int src ^ "]"))
                (Str.global_replace
                    (Str.regexp_string "{0}")
                    ("[" ^ (string_of_int dst) ^ "]")
                    x))
        in
        Var new_name
    | Aux i   -> f
    | Not g   -> Not (replace_placeholders g src dst)
    | Or children  ->
        Or (List.rev_map (fun f -> replace_placeholders f src dst) children)
    | And children  ->
        And (List.rev_map (fun f -> replace_placeholders f src dst) children)


(*
    Inject a literal into every clause of CNF.
    It is useful for implementation of the constraint
    back[i] -> T(k, i), where T(k, i) is in CNF.
 *)
let rec inject_lit_into_cnf f new_lit =
    match f with
      True    -> True
    | False   -> raise (Invalid_argument "inject_lit_into_cnf: unexpected False")
    | Var x   -> Or [new_lit; f]
    | Aux i   -> Or [new_lit; f]
    | Not g   -> Or [new_lit; f]
    | Or lits  -> Or (new_lit :: lits)
    | And children  ->
        And (List.rev_map (fun f -> inject_lit_into_cnf f new_lit) children)


let cnf_to_text cnf_f =
  let clauses = (cnf_to_lst cnf_f) in
  let fmt_lit l =
    match l with
      | True  -> ""
      | False -> "FALSE"
      | Var x -> x
      | Aux i -> "_" ^ (string_of_int i)
      | Not (Var x) -> "~" ^ x
      | Not (Aux i) -> "~" ^ (string_of_int i)
      | l -> raise (Invalid_argument ("Not a literal"))
  in
  (List.fold_left
       (fun s c -> (if s = "" then "" else s ^ ", ")
   ^ (List.fold_left (fun x y -> (if x = "" then y else x ^ " + " ^ y)) ""
        (List.rev_map (fun l -> (fmt_lit l) ^ "") c)))
       "" clauses)


let collect_vars forms =
    let rec collect set = function
        | True -> set
        | False -> set
        | Var x -> StringSet.add x set
        | Aux _ -> set
        | Not g -> collect set g
        | Or gs -> List.fold_left collect set gs
        | And gs -> List.fold_left collect set gs
    in
    StringSet.elements (List.fold_left collect StringSet.empty forms)

