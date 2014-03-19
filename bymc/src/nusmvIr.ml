(* An intermediate represenation for the flat subset of NuSMV *)
(*                                                            *)
(* Igor Konnov, 2013                                          *)

open Printf

open Accums

exception Smv_error of string

type Smv_type_t = SMV_INT | SMV_BOOL

let smv_type_s = function
    | SMV_INT -> "integer"
    | SMV_BOOL -> "boolean"


class smv_var name_i var_id =
    object(self)
        method id = var_id
        method name = name_i
    end


type 't smv_expr_t =
    | EInt of int
    | EBool of bool
    | EVar of smv_var
    | E1 of 't * 't smv_expr_t
    | E2 of 't * 't smv_expr_t * 't smv_expr
    | ECase of ('t smv_expr_t * 't smv_expr) list


type 't section_t =
    | SDefine of (smv_var * 't smv_expr) list
    | STrans of 't smv_expr list
    | SInit of 't smv_expr list
    | SInvar of 't expr list
    (* normal variable, not a module *)
    | SVar of (smv_var * Smv_type_t) list
    (* module instance (never happens in the flat representation) *)
    | SModInst of string * string * (token expr list)


type top_t =
    | SModule of string * (var list) * (section_t list)
    | SLtlSpec of string * token expr
    | SInvarSpec of string * token expr
    | SJustice of token expr
    | SCompassion of token expr

