open Ctypes
open Foreign

let create =
    foreign "mathsat_create" (void @-> returning int)

let destroy =
    foreign "mathsat_destroy" (int @-> returning void)

let declare_int =
    foreign "mathsat_declare_int" (int @-> string @-> returning void)

let massert =
    foreign "mathsat_assert" (int @-> string @-> returning int)

let solve =
    foreign "mathsat_solve" (int @-> returning int)


let _ =
    (* register the functions *)
    Msat.is_loaded := true;
    Msat.p_create := create;
    Msat.p_destroy := destroy;
    Msat.p_declare_int := declare_int;
    Msat.p_assert := massert;
    Msat.p_solve := solve;

