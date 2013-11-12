(*
 Translating processes in SSA and encoding them in NuSMV format.
 This is the third try to create an efficient encoding in NuSMV.
 *)

open Printf

open Nusmv

let module_of_proc rt xd_prog proc =
    Module (proc#get_name, [], [])

let transform rt out_name intabs_prog =
    let xd_prog = SmtXducerPass.do_xducers rt#caches intabs_prog in
    let tops =
        List.map (module_of_proc rt xd_prog) (Program.get_procs xd_prog) in
    let out = open_out (out_name ^ ".smv") in
    List.iter (fun t -> fprintf out "%s\n" (top_s t)) tops;
    close_out out

