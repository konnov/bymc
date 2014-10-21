open Ctypes

let start =
    foreign "start" (void @-> returning int)

let stop =
    foreign "start" (void @-> returning int)

