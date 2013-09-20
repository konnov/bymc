(* Plugin infrastructure to allow the user running different workflows.
 *
 * Igor Konnov, 2013
 *)

open Program
open Spin
open SpinIr

exception Plugin_error of string

class plugin_t =
    object
        val mutable m_ready

        method is_ready = m_ready
        method set_ready = m_ready <- true
    end


class transform_plugin_t =
    object
        inherit plugin_t

        val mutable m_in = Program.empty
        val mutable m_out = Program.empty

        method virtual transform: program_t -> program_t
        method virtual decode_trail: path_t -> path_t
        method virtual refine: path_t -> bool
    end


class analysis_plugin_t =
    object
        inherit plugin_t

        val mutable m_in = Program.empty
        method virtual apply: program_t -> bool
    end

