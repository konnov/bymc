(* Encoding a CFG as an SMT formula, assuming that CFG is in SSA. *)

open Spin;;
open Spin_ir;;
open Spin_ir_imp;;
open Cfg;;
open Ssa;;
open Smt;;

let cfg_to_form cfg =
;;
