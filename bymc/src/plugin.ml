(* Plugin infrastructure to allow the user running different workflows.
 *
 * Igor Konnov, 2013
 *)

open Program
open Runtime
open Spin
open SpinIr

exception Plugin_error of string

class plugin_t =
    object
        val mutable m_ready = false

        method is_ready = m_ready
        method set_ready = m_ready <- true
    end


class empty_container =
    object
        method get_plugin (name: string): plugin_t =
            raise (Plugin_error "No plugin container")
    end


class virtual transform_plugin_t =
    object
        inherit plugin_t

        val mutable m_in = Program.empty
        val mutable m_out = Program.empty

        method set_input input = m_in <- input
        method get_input = m_in

        method set_output output = m_out <- output
        method get_output = m_out

        method virtual transform: runtime_t -> program_t -> program_t
        method virtual decode_trail: runtime_t -> path_t -> path_t
        method virtual refine: runtime_t -> path_t -> bool * path_t
    end


class virtual analysis_plugin_t =
    object
        inherit transform_plugin_t

        method decode_trail _ path = path

        method refine _ path = (false, path)
    end


class plugin_chain_t =
    object(self)
        inherit transform_plugin_t

        val mutable m_plugins: (string * transform_plugin_t) list = []

        method add_plugin name plugin =
            m_plugins <- List.rev ((name, plugin) :: (List.rev m_plugins))

        method get_plugin name =
            try
                let _, p = List.find (fun (n, _) -> name = n) m_plugins in
                if not p#is_ready
                then raise (Plugin_error ("Plugin " ^ name ^ " is not ready"));
                (p :> plugin_t)
            with Not_found ->
                raise (Plugin_error ("Not found " ^ name))

        method transform rtm prog =
            let apply input (_, plugin) =
                plugin#transform rtm input
            in
            self#set_input prog;
            self#set_output (List.fold_left apply prog m_plugins);
            self#get_output

        method refine rtm path =
            let do_refine (status, path_cons) (_, plugin) =
                if status
                then (true, path_cons)
                else plugin#refine rtm path_cons
            in
            List.fold_left do_refine (false, path) (List.rev m_plugins)

        method decode_trail rtm _ =
            raise (Plugin_error "Not supported: decode_trail")

    end
