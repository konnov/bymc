(*
  General functions related to abstraction to keep specialized abstractions simpler.
  
  Igor Konnov, 2012
 *)

open Printf;;

open Spin;;
open SpinIr;;
open SpinIrImp;;

exception Abstraction_error of string;;

type abs_type = ExistAbs | UnivAbs;;

(* each expression is characterized by its trait w.r.t. abstraction *)
type expr_abs_trait =
    ConstExpr  (* a constant expression, may be abstracted *)
  | ConcExpr   (* an expression that has concrete variables *)
  | AbsExpr    (* an expression that has abstracted variables *)
  | MixExpr    (* an expression that has both concrete and abstracted variables *)
  | ShadowExpr (* do not touch this expression *)
;;

let get_abs_trait
        (var_trait_fun: var -> expr_abs_trait) (ex: 't expr) : expr_abs_trait =
    let rec explore = function
        | Const _ -> ConstExpr
        | Var v -> var_trait_fun v
        | UnEx (tok, arg) -> explore arg
        | BinEx (PLUS, lhs, rhs)
        | BinEx (MINUS, lhs, rhs)
        | BinEx (MULT, lhs, rhs)
        | BinEx (DIV, lhs, rhs) as e ->
            let lt = (explore lhs) and rt = (explore rhs) in
            if lt <> rt && lt != ConstExpr && rt != ConstExpr
            then let m = sprintf "Concrete and abstracted variables are mixed in %s"
                        (expr_s e) in
                raise (Abstraction_error m)
            else lt

        | BinEx (_, lhs, rhs) ->
            let lt = (explore lhs) and rt = (explore rhs) in
            begin
                match lt, rt with
                | _, ShadowExpr
                | ShadowExpr, _ -> ShadowExpr
                | ConstExpr, (_ as t)
                | (_ as t), ConstExpr -> t
                | ConcExpr, ConcExpr -> ConcExpr
                | AbsExpr, AbsExpr -> AbsExpr
                | ConcExpr, AbsExpr
                | AbsExpr, ConcExpr
                | _, MixExpr
                | MixExpr, _ -> MixExpr
            end

        | _ -> ShadowExpr
    in
    explore ex
;;
