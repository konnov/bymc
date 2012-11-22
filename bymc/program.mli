(*
  Convenient representation of an (extended) Promela program to simplify
  analysis and transformation passes.

  Igor Konnov, 2012
 *)

module StringMap = Map.Make (String)

(*
  Representation of a program under analysis and transformation.
 *)
class type Program =
    object(self)
        (* TODO: the fields must go to the implementation! *)

        (* global declarations *)
        val params: var list
        val shared: var list

        (* assumptions *)
        val assumps: Spin.token expr list

        (* processes *)
        val procs: Spin.token proc StringMap

        (* atomic propositions *)
        val atomics: Spin.token expr StringMap

        (* ltl formulas *)
        val ltl_forms: Spin.token expr StringMap
    end
;;

