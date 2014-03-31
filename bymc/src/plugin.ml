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
    object(self)
        inherit plugin_t plugin_name

        val mutable m_ins: Program.program_t list = []
        val mutable m_out = Program.empty

        method set_inputs inputs = m_ins <- inputs
        method get_input no =
            try List.nth m_ins no
            with Failure _ ->
                let m = Printf.sprintf
                    "Required input no. %d, but %s has inputs up to %d"
                    no plugin_name ((List.length m_ins) - 1) in
                raise (Plugin_error m)

        method get_input0 = self#get_input 0
        method get_input1 = self#get_input 1

        method set_output output = m_out <- output
        method get_output = m_out

        method virtual transform: runtime_t -> program_t
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


(* this type specify the plugin's input from the other plugins *)
type input_t =
     (* take the output of the predecessor *)
    | OutOfPred 
     (* take the output of a plugin *)
    | OutOfPlugin of string
     (* take the output of several plugins *)
    | OutOfPlugins of string list


class plugin_chain_t =
    object(self)
        val mutable m_plugins: (transform_plugin_t * input_t) list = []
        val mutable m_queue: (transform_plugin_t * input_t) list = []
        val mutable m_in = Program.empty
        val mutable m_out = Program.empty

        method get_input = m_in
        method get_output = m_out

        method add_plugin: 'a  . (#transform_plugin_t as 'a) -> input_t -> unit =
            fun plugin inpspec ->
                let tp = (plugin :> transform_plugin_t) in
                m_plugins <- List.rev ((tp, inpspec) :: (List.rev m_plugins))

        method private find_transform_plugin name =
            try
                let p, _ = List.find (fun (p, _) -> p#name = name) m_plugins in
                if not p#is_ready
                then raise (Plugin_error ("Plugin " ^ name ^ " is not ready"));
                p
            with Not_found ->
                raise (Plugin_error ("Not found " ^ name))

        method find_plugin name =
            let p = self#find_transform_plugin name in
            (p :> plugin_t)

        method update_runtime rt =
            let update (p, _) =
                if not (p#is_disabled rt)
                then p#update_runtime rt
            in
            List.iter update m_plugins

            (* FIX *)
        method private apply_plugin rt pred_out (plugin, inpspec) =
            let inputs = match inpspec with
            | OutOfPred -> [pred_out]
            | OutOfPlugin name ->
                let p = self#find_transform_plugin name in
                [ p#get_output ]
            | OutOfPlugins names  ->
                let plugins = List.map self#find_transform_plugin names in
                List.map (fun p -> p#get_output) plugins
            in
            plugin#set_inputs inputs;
            let plugin_out = if plugin#is_disabled rt
                then pred_out
                else plugin#transform rt in
            plugin#set_ready;
            plugin#set_output plugin_out;
            if not (plugin#is_disabled rt)
            then plugin#update_runtime rt;
            plugin_out

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
                | (p, inpspec) :: tl ->
                    (* InputRequired may be thrown here *)
                    let plugin_out = self#apply_plugin rt m_out (p, inpspec) in
                    m_out <- plugin_out;
                    m_queue <- tl;
                    apply tl

                | [] -> ()
            in
            apply m_queue;
            m_out

        method refine rt path =
            let do_refine (status, trail, queue) (p, inpspec) =
                if status
                then (true, trail, queue)
                else if not (p#is_disabled rt)
                    then begin
                        let new_trail = p#decode_trail rt trail in
                        let res, new_prog = p#refine rt new_trail in
                        if res
                        then begin
                            p#set_output new_prog;
                            (res, new_trail, (p, inpspec) :: queue)
                        end else (res, new_trail, (p, inpspec) :: queue)
                    end else (false, trail, queue)
            in
            let res, _, queue =
                List.fold_left do_refine (false, path, []) (List.rev m_plugins)
            in
            if res
            then begin
                match queue with
                | (p, _) :: tl ->
                    m_out <- List.fold_left (self#apply_plugin rt) p#get_output tl
                | _ -> raise (Failure "empty plugin queue")
            end;
            (res, m_out)

    end
