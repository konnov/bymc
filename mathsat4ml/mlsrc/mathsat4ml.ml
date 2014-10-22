open Ctypes
open Foreign

let start =
    foreign "mathsat_start" (void @-> returning int)

let stop =
    foreign "mathsat_stop" (void @-> returning int)


let _ =
    (* register itself *)
    Foo.foo_int := 1;
    Foo.p_start := start;
    Foo.p_stop := stop

