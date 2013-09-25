(* Plugin infrastructure to allow the user running different workflows.
 *
 * Igor Konnov, 2013
 *)

open Program
open Runtime
open Spin
open SpinIr

exception Plugin_error of string

(* the generic plugin *)
class plugin_t (plugin_name: string) =
    object
        val mutable m_ready = false

        method is_ready = m_ready
        method set_ready = m_ready <- true

        method name = plugin_name

        method is_disabled (rt: runtime_t) = false

        method has_opt (rt: runtime_t) (name: string) =
            let fullname = plugin_name ^ "." ^ name in
            let options = (rt#caches#options).Options.plugin_opts in
            Options.StringMap.mem fullname options

        method get_opt (rt: runtime_t) (name: string) =
            let fullname = plugin_name ^ "." ^ name in
            let options = (rt#caches#options).Options.plugin_opts in
            try Options.StringMap.find fullname options
            with Not_found ->
                raise (Plugin_error ("Plugin option " ^ fullname ^ " not found"))
    end


class virtual transform_plugin_t (plugin_name: string) =
    object
        inherit plugin_t plugin_name

        val mutable m_in = Program.empty
        val mutable m_out = Program.empty

        method set_input input = m_in <- input
        method get_input = m_in

        method set_output output = m_out <- output
        method get_output = m_out

        method virtual transform: runtime_t -> program_t -> program_t
        method virtual update_runtime: runtime_t -> unit
        method virtual decode_trail: runtime_t -> path_t -> path_t
        method virtual refine: runtime_t -> path_t -> bool * path_t
    end


class virtual analysis_plugin_t (plugin_name: string) =
    object
        inherit transform_plugin_t plugin_name

        method decode_trail _ path = path

        method refine _ path = (false, path)
    end


class plugin_chain_t =
    object(self)
        val mutable m_plugins: transform_plugin_t list = []
        val mutable m_in = Program.empty
        val mutable m_out = Program.empty

        method get_input = m_in
        method get_output = m_out

        method add_plugin: 'a  . (#transform_plugin_t as 'a) -> unit =
            fun plugin ->
                let tp = (plugin :> transform_plugin_t) in
                m_plugins <- List.rev (tp :: (List.rev m_plugins))

        method find_plugin name =
            try
                let p = List.find (fun p -> p#name = name) m_plugins in
                if not p#is_ready
                then raise (Plugin_error ("Plugin " ^ name ^ " is not ready"));
                (p :> plugin_t)
            with Not_found ->
                raise (Plugin_error ("Not found " ^ name))

        method transform rt prog =
            let apply input plugin =
                plugin#set_input input;
                let out = if plugin#is_disabled rt
                    then input
                    else plugin#transform rt input in
                plugin#set_output out;
                if not (plugin#is_disabled rt) then plugin#update_runtime rt;
                out
            in
            m_in <- prog;
            m_out <- (List.fold_left apply prog m_plugins);
            m_out

        method refine rt path =
            let do_refine (status, path_cons) plugin =
                if status
                then (true, path_cons)
                else plugin#refine rt path_cons
            in
            List.fold_left do_refine (false, path) (List.rev m_plugins)

    end
