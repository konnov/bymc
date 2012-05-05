open Spin_ir;;
open Spin_ir_imp;;


class ['t] basic_block =
    object
        val mutable seq: 't stmt list = []
        val mutable succ: 't basic_block list = []
    end
;;

