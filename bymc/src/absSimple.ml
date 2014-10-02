(* Very simple abstractions are collected here *)

open Printf

open Simplif
open Spin
open SpinIr
open SpinIrImp

(*
 Remove the variables recognized by is_nuked from the expression, i.e.,
 replace any arithmetic expressions involving 'foo' with TRUE.
 It is somewhat similar to infinite data abstraction in CMP by McMillan. *)
let nuke_vars is_nuked exp =
    let rec red = function
    | Var v ->
            if is_nuked v
            then (Var v, true)
            else (Var v, false)

    | IntConst i ->
            (IntConst i, false)

    | BinEx (PLUS as t, l, r)
    | BinEx (MINUS as t, l, r)
    | BinEx (MULT as t, l, r)
    | BinEx (DIV as t, l, r)
    | BinEx (MOD as t, l, r) ->
            let nl, nukel = red l and nr, nuker = red r in
            if nukel || nuker
            then (IntConst 1, true)
            else (BinEx (t, nl, nr), false)

    | BinEx (EQ as t, l, r)
    | BinEx (NE as t, l, r)
    | BinEx (LE as t, l, r)
    | BinEx (GE as t, l, r)
    | BinEx (LT as t, l, r)
    | BinEx (GT as t, l, r) ->
            let nl, nukel = red l and nr, nuker = red r in
            if nukel || nuker
            then (IntConst 1, false)
            else (BinEx (t, nl, nr), false)

    | BinEx (t, l, r) ->
            let nl, _ = red l and nr, _ = red r in
            (BinEx (t, nl, nr), false)

    (*  next(x) in nusmv *)
    | UnEx (NEXT, e) ->
            let ne, nukee = red e in
            if nukee
            then (IntConst 1, true)
            else (UnEx (NEXT, ne), false)

    | UnEx (t, e) ->
            let ne, _ = red e in
            (UnEx (t, ne), false)

    | _ as e -> (e, false)
    in
    compute_consts (fst (red exp))
   
