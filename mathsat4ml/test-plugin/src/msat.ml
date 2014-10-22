let is_loaded = ref false

let p_create = ref (fun () -> 0)
let p_destroy = ref (fun (_: int) -> ())

