class type proc_struc =
    object
        method get_regions: string -> Regions.region_tbl
        method set_regions: string -> Regions.region_tbl -> unit
        method get_annotations: (int, SpinIr.annot_t) Hashtbl.t
    end


val empty_proc_struc: unit -> proc_struc    

val extract_skel: Spin.token SpinIr.mir_stmt list -> Regions.region_tbl    
val compute_struc: Program.program_t -> proc_struc    

