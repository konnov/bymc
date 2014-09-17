val is_error_path:
    Runtime.runtime_t
        -> SpinIr.data_type_tab
        -> SymbSkel.Sk.skel_t
        -> Spin.token SpinIr.expr
        -> PorBounds.path_t
        -> bool
