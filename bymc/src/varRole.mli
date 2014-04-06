type var_role =
    | BoundedInt of int * int | SharedBoundedInt of int * int
    | SharedUnbounded | LocalUnbounded | Scratch of SpinIr.var

exception Role_error of string
exception Var_not_found of string

val var_role_s: var_role -> string

val is_unbounded: var_role -> bool
val is_bounded: var_role -> bool
val is_scratch: var_role -> bool
val is_local_unbounded: var_role -> bool
val is_shared_unbounded: var_role -> bool

class var_role_tbl:
    object
        method add_from_hash: (SpinIr.var, var_role) Hashtbl.t -> unit
        method get_role: SpinIr.var -> var_role
        method add: SpinIr.var -> var_role -> unit
        (* TODO: hide it *)
        method add_by_id: int -> var_role -> unit
        method copy: var_role_tbl
    end


val identify_var_roles: Program.program_t -> var_role_tbl

