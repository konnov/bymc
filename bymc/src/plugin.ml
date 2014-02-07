(* Plugin infrastructure to allow the user running different workflows.
 *
 * Igor Konnov, 2013-2014
 *)

open Program
open Runtime
open Spin
open SpinIr

exception Plugin_error of string
exception InputRequired of string

(* a generic plugin *)
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
        method virtual decode_trail: runtime_t -> lasso_t -> lasso_t
        method virtual refine: runtime_t -> lasso_t -> bool * program_t
    end


class virtual analysis_plugin_t (plugin_name: string) =
    object(self)
        inherit transform_plugin_t plugin_name

        method decode_trail _ path = path

        method refine _ path = (false, self#get_output)
    end


class plugin_chain_t =
    object(self)
        val mutable m_plugins: transform_plugin_t list = []
        val mutable m_queue: transform_plugin_t list = []
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

        method update_runtime rt =
            let update p =
                if not (p#is_disabled rt)
                then p#update_runtime rt
            in
            List.iter update m_plugins

        method private apply_plugin rt input plugin =
            plugin#set_input input;
            let out = if plugin#is_disabled rt
                then input
                else plugin#transform rt input in
            plugin#set_output out;
            if not (plugin#is_disabled rt)
            then plugin#update_runtime rt;
            out

        method transform rt prog =
            m_in <- prog;
            if m_queue = []
            then begin
                m_queue <- m_plugins;
                m_out <- m_in
            end;
            (* else we continue the transformation *)

            (* this strange loop is needed, as a plugin may throw
               InputRequired exception *)
            let rec apply = function
                | p :: tl ->
                    (* InputRequired may be thrown here *)
                    let out = self#apply_plugin rt m_out p in
                    m_out <- out;
                    m_queue <- tl;
                    apply tl

                | [] -> ()
            in
            apply m_queue;
            m_out

        method refine rt path =
            let do_refine (status, trail, queue) p =
                if status
                then (true, trail, queue)
                else if not (p#is_disabled rt)
                    then begin
                        let new_trail = p#decode_trail rt trail in
                        let res, new_prog = p#refine rt new_trail in
                        if res
                        then begin
                            p#set_output new_prog;
                            (res, new_trail, p :: queue)
                        end else (res, new_trail, p :: queue)
                    end else (false, trail, queue)
            in
            let res, _, queue =
                List.fold_left do_refine (false, path, []) (List.rev m_plugins)
            in
            if res
            then begin
                let hd, tl = List.hd queue, List.tl queue in 
                m_out <- List.fold_left (self#apply_plugin rt) hd#get_output tl
            end;
            (res, m_out)

    end
