open Spin
open SpinIr
open VarRole

(* Context of parametric interval abstraction.
   It collects variable roles over different process prototypes.
 *)
class pia_data_ctx roles =
    object(self)
        val mutable m_hack_shared: bool = false

        method is_hack_shared = m_hack_shared
        method set_hack_shared b = m_hack_shared <- b

        method must_keep_concrete (e: token expr) = 
            match e with
            | Var v -> m_hack_shared && is_shared_unbounded (roles#get_role v)
            | _ -> false

        method var_needs_abstraction (v: var) =
            let r = roles#get_role v in
            (not (self#must_keep_concrete (Var v))) && (not (is_bounded r))
    end
;;

