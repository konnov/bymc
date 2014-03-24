
type loop_sig

val empty_loop_sig: loop_sig

(* the following regions are currently extracted:
    decl, init, loop_prefix, comp, update, loop_body
 *)

class type proc_struc =
    object
        method get_regions: string -> Regions.region_tbl
        method set_regions: string -> Regions.region_tbl -> unit
        method get_annotations: (int, SpinIr.annot_t) Hashtbl.t
        method get_loop_sig: string -> loop_sig
        method set_loop_sig: string -> loop_sig -> unit
    end

val empty_proc_struc: unit -> proc_struc    

val extract_skel: Spin.token SpinIr.mir_stmt list -> Regions.region_tbl    
val compute_struc: Program.program_t -> proc_struc    

val extract_loop_sig: Program.program_t -> Regions.region_tbl
    -> Spin.token SpinIr.proc -> loop_sig

val get_prev_next: loop_sig -> (SpinIr.var * SpinIr.var) list

val get_loop_next: loop_sig -> SpinIr.var -> SpinIr.var

