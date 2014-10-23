let is_loaded = ref false

let p_create = ref (fun () -> 0)
let p_destroy = ref (fun (_: int) -> ())
let p_declare_int = ref (fun (_: int) (_: string) -> ())
let p_assert = ref (fun (_: int) (_: string) -> 0)
let p_solve = ref (fun (_: int) -> 0)

