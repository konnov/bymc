open Printf

open Debug
open Instantiation
open Options
open Parse
open Plugin
open Program
open Runtime
open Spin
open SpinIr
open Writer

class instantiation_plugin_t (plugin_name: string) =
    object(self)
        inherit transform_plugin_t plugin_name

        method transform rt prog =
            let opts = rt#caches#options in
            let units = units_of_program prog in
            let new_units = do_substitution opts.param_assignments units in
            write_to_file true "concrete.prm" new_units (get_type_tab prog);
            program_of_units (new data_type_tab) new_units

        method update_runtime rt = ()

        method decode_trail _ path = path

        method refine _ path = (false, path)
    end

