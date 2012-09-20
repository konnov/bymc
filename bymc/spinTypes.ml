type var_type = TBIT | TBYTE | TSHORT
    | TINT | TUNSIGNED | TCHAN | TMTYPE | TPROPOSITION;;
type xu_type = XS | XR;;

let var_type_s tp =
    match tp with
      TBIT -> "BIT"
      | TBYTE -> "BYTE"
      | TSHORT -> "SHORT"
      | TINT -> "INT"
      | TUNSIGNED -> "UNSIGNED"
      | TCHAN -> "CHAN"
      | TMTYPE -> "MTYPE"
      | TPROPOSITION -> "PROPOSITION"
;;

let xu_type_s tp =
    match tp with
      XS -> "XS"
      | XR -> "XR"
;;

