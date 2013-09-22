exception Plugin_error of string

class type plugin_t =
    object
        method is_ready: bool
        method set_ready: unit
    end


class type plugin_container_t =
    object
        method get_plugin: string -> plugin_t
    end


class type virtual transform_plugin_t =
    object
        inherit plugin_t

        method set_input: Program.program_t -> unit
        method get_input: Program.program_t

        method set_output: Program.program_t -> unit
        method get_output: Program.program_t

        method virtual transform:
            Runtime.runtime_t -> Program.program_t -> Program.program_t

        method virtual decode_trail:
            Runtime.runtime_t -> Program.path_t -> Program.path_t

        method virtual refine:
            Runtime.runtime_t -> Program.path_t -> bool * Program.path_t            
    end


class type virtual analysis_plugin_t =
    object
        inherit transform_plugin_t

        method decode_trail:
            Runtime.runtime_t -> Program.path_t -> Program.path_t

        method refine:
            Runtime.runtime_t -> Program.path_t -> bool * Program.path_t
    end


class type plugin_chain_t =
    object
        inherit transform_plugin_t

        method add_plugin: string -> transform_plugin_t -> unit

        method get_plugin: string -> plugin_t

        method transform:
            Runtime.runtime_t -> Program.program_t -> Program.program_t

        method decode_trail:
            Runtime.runtime_t -> Program.path_t -> Program.path_t

        method refine:
            Runtime.runtime_t -> Program.path_t -> bool * Program.path_t            
    end
