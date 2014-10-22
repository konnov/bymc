open Ctypes
open Foreign

let create =
    foreign "mathsat_create" (void @-> returning int)

let destroy =
    foreign "mathsat_destroy" (int @-> returning void)


let _ =
    (* register itself *)
    Msat.is_loaded := true;
    Msat.p_create := create;
    Msat.p_destroy := destroy

