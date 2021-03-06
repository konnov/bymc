val is_loaded: bool ref

val p_create: (unit -> int) ref
val p_destroy: (int -> unit) ref
val p_declare_int: (int -> string -> unit) ref
val p_assert: (int -> string -> int) ref
val p_solve: (int -> int) ref
val p_push: (int -> unit) ref
val p_pop: (int -> unit) ref
val p_get_model_value: (int -> string -> string) ref

