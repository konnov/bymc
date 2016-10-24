
(**
  An abstraction of a plugin that produces a TA, e.g., SymbSkel.symb_skel_t
 *)
class virtual ta_source_t =
    object
        (**
          Get the constructed TA.
          *)
        method virtual get_ta: SymbSkel.Sk.skel_t
    end

