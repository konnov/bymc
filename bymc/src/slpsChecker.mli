val is_error_tree:
    Runtime.runtime_t
        -> SpinIr.data_type_tab
        -> SymbSkel.Sk.skel_t
        -> (unit -> unit)
        -> Spin.token SpinIr.expr
        -> PorBounds.T.schema_tree_t
        -> bool
