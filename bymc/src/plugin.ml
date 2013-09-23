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
class plugin_t =
    object
        val mutable m_ready = false

        method is_ready = m_ready
        method set_ready = m_ready <- true
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
        method virtual update_runtime: runtime_t -> unit
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
        val mutable m_plugins: (string * transform_plugin_t) list = []
        val mutable m_in = Program.empty
        val mutable m_out = Program.empty

        method get_input = m_in
        method get_output = m_out

        method add_plugin: 'a  . (#transform_plugin_t as 'a) -> string -> unit =
            fun plugin name ->
                let tp = (plugin :> transform_plugin_t) in
                m_plugins <- List.rev ((name, tp) :: (List.rev m_plugins))

        method find_plugin name =
            try
                let _, p = List.find (fun (n, _) -> name = n) m_plugins in
                if not p#is_ready
                then raise (Plugin_error ("Plugin " ^ name ^ " is not ready"));
                (p :> plugin_t)
            with Not_found ->
                raise (Plugin_error ("Not found " ^ name))

        method transform rtm prog =
            let apply input (_, plugin) =
                let out = plugin#transform rtm input in
                plugin#update_runtime rtm;
                out
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
