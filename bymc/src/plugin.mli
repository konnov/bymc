exception Plugin_error of string

class plugin_t: string ->
    object
        method is_ready: bool
        method set_ready: unit
        method name: string

        method is_disabled: Runtime.runtime_t -> bool

        method has_opt: Runtime.runtime_t -> string -> bool
        method get_opt: Runtime.runtime_t -> string -> string
    end


class virtual transform_plugin_t: string ->
    object
        inherit plugin_t

        method set_input: Program.program_t -> unit
        method get_input: Program.program_t

        method set_output: Program.program_t -> unit
        method get_output: Program.program_t

        (* transform the program *)
        method virtual transform:
            Runtime.runtime_t -> Program.program_t -> Program.program_t

        (* update the caches with the computed results *)
        method virtual update_runtime:
            Runtime.runtime_t -> unit

        (* decode a counter-example *)
        method virtual decode_trail:
            Runtime.runtime_t -> Program.lasso_t -> Program.lasso_t

        (* refine the current program using the decoded path,
           return true if successful *)
        method virtual refine:
            Runtime.runtime_t -> Program.lasso_t -> bool * Program.program_t
    end


class virtual analysis_plugin_t: string ->
    object
        inherit transform_plugin_t

        method decode_trail:
            Runtime.runtime_t -> Program.lasso_t -> Program.lasso_t
        method refine:
            Runtime.runtime_t -> Program.lasso_t -> bool * Program.program_t
    end


class plugin_chain_t:
    object
        method add_plugin: (#transform_plugin_t as 'a) -> unit

        method find_plugin: string -> plugin_t

        method transform:
            Runtime.runtime_t -> Program.program_t -> Program.program_t

        (* update the caches with the computed results *)
        method update_runtime:
            Runtime.runtime_t -> unit

        method refine:
            Runtime.runtime_t -> Program.lasso_t -> bool * Program.program_t            
        method get_input: Program.program_t

        method get_output: Program.program_t

    end

