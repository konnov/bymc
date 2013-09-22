(* Plugin infrastructure to allow the user running different workflows.
 *
 * Igor Konnov, 2013
 *)

open Program
open Runtime
open Spin
open SpinIr

exception Plugin_error of string

class type plugin_t =
    object
        method is_ready: bool
        method set_ready: unit
        method get_plugin: string -> plugin_t
    end


(* the actual plugin container type *)
class virtual plugin_container_t =
    object
        method virtual find_plugin: string -> plugin_t
    end

(* the default implementation *)
class empty_container =
    object
        inherit plugin_container_t

        method find_plugin (name: string): plugin_t =
            raise (Plugin_error "No plugin container")
    end


(* the generic plugin *)
class plugin_impl =
    object
        val mutable m_container: plugin_container_t = new empty_container

        val mutable m_ready = false

        method is_ready = m_ready
        method set_ready = m_ready <- true

        method set_container ctr = m_container <- ctr
        method get_plugin (name: string): plugin_t =
            m_container#find_plugin name
    end


class virtual transform_plugin_t =
    object
        inherit plugin_impl

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
        inherit plugin_container_t

        val mutable m_plugins: (string * transform_plugin_t) list = []
        val mutable m_in = Program.empty
        val mutable m_out = Program.empty

        method get_input = m_in
        method get_output = m_out

        method add_plugin name plugin =
            plugin#set_container (self :> plugin_container_t);
            m_plugins <- List.rev ((name, plugin) :: (List.rev m_plugins))

        method find_plugin name =
            try
                let _, p = List.find (fun (n, _) -> name = n) m_plugins in
                if not p#is_ready
                then raise (Plugin_error ("Plugin " ^ name ^ " is not ready"));
                ((p :> plugin_impl) :> plugin_t)
            with Not_found ->
                raise (Plugin_error ("Not found " ^ name))

        method transform rtm prog =
            let apply input (_, plugin) =
                plugin#transform rtm input
            in
            m_in <- prog;
            m_out <- (List.fold_left apply prog m_plugins);
            m_out

        method refine rtm path =
            let do_refine (status, path_cons) (_, plugin) =
                if status
                then (true, path_cons)
                else plugin#refine rtm path_cons
            in
            List.fold_left do_refine (false, path) (List.rev m_plugins)

    end
