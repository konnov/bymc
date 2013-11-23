open Printf

open Spin
open SpinIr
open SpinIrImp

type eval_res = Bool of bool | Int of int

exception Eval_error of string

let rec eval_expr val_fun e =
    let ubool = function
        | Bool b -> b
        | _ -> raise (Eval_error ("expected bool"))
    in
    let uint = function
        | Int i -> i
        | _ -> raise (Eval_error ("expected int"))
    in
    match e with
    | Const value ->
            Int value
    | Var v ->
            Int (val_fun e)
    | BinEx (ARR_ACCESS, Var _, Const _) ->
            Int (val_fun e)
    | BinEx (EQ, le, re) ->
            let lv = uint (eval_expr val_fun le) in
            let rv = uint (eval_expr val_fun re) in
            (Bool (lv = rv))
    | BinEx (NE, le, re) ->
            let lv = uint (eval_expr val_fun le) in
            let rv = uint (eval_expr val_fun re) in
            (Bool (lv <> rv))
    | BinEx (GT, le, re) ->
            let lv = uint (eval_expr val_fun le) in
            let rv = uint (eval_expr val_fun re) in
            (Bool (lv > rv))
    | BinEx (GE, le, re) ->
            let lv = uint (eval_expr val_fun le) in
            let rv = uint (eval_expr val_fun re) in
            (Bool (lv >= rv))
    | BinEx (LT, le, re) ->
            let lv = uint (eval_expr val_fun le) in
            let rv = uint (eval_expr val_fun re) in
            (Bool (lv < rv))
    | BinEx (LE, le, re) ->
            let lv = uint (eval_expr val_fun le) in
            let rv = uint (eval_expr val_fun re) in
            (Bool (lv <= rv))
    | BinEx (AND, le, re) ->
            let lv = ubool (eval_expr val_fun le) in
            let rv = ubool (eval_expr val_fun re) in
            (Bool (lv && rv))
    | BinEx (OR, le, re) ->
            let lv = ubool (eval_expr val_fun le) in
            let rv = ubool (eval_expr val_fun re) in
            (Bool (lv || rv))
    | UnEx (NEG, l) ->
            (Bool (not (ubool (eval_expr val_fun e))))

    | BinEx (MINUS, le, re) ->
            let lv = uint (eval_expr val_fun le) in
            let rv = uint (eval_expr val_fun re) in
            (Int (lv - rv))
    | BinEx (PLUS, le, re) ->
            let lv = uint (eval_expr val_fun le) in
            let rv = uint (eval_expr val_fun re) in
            (Int (lv + rv))
    | BinEx (MULT, le, re) ->
            let lv = uint (eval_expr val_fun le) in
            let rv = uint (eval_expr val_fun re) in
            (Int (lv * rv))
    | BinEx (DIV, le, re) ->
            let lv = uint (eval_expr val_fun le) in
            let rv = uint (eval_expr val_fun re) in
            (Int (lv / rv))

    | _ as e ->
        raise (Eval_error
            (sprintf "Unknown expression to evaluate: %s" (expr_s e)))

