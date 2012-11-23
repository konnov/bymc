(* Analysis and transformation infrastructure.

   Igor Konnov, 2012
 *)

open VarRole;;

exception CacheStateError of string;;

(*
  All analysis and transformation passes have an access to this cache.
  Every pass may update the attributes of this cache. If a pass corrupts certain
  cached data, then the pass must reset this data.
 *)
class AnalysisCache =
    object(self)
        (* variable roles *)
        val mutable var_roles: (var, var_role) Hashtbl.t option = Hashtbl.create 1
        val mutable pia_dom: pia_domain
        (* PIADataAbsCtx *)
        (* PIACounterAbsCtx *)
    end
;;


(*
  All analysis and transformation passes have an access to this cache,
  and every pass may update the attributes of this cache. The purpose of the
  cache is to collect the structural information about control flow and data
  flow. If a pass corrupts certain cached data, then the pass must reset this
  data.
 *)
class ProcStrucCache =
    object(self)
        (* statements *)
        (* regions *)
    end
;;


class PassCaches =
    object(self)
        (* analysisCache: AnalysisCache *)
        (* procStrucCaches: string -> ProcStructCache *)
    end
;;

type analysis_fun = PassCaches -> Program -> PassCaches;;
type translation_fun = PassCaches -> Program -> (PassCaches * Program);;

