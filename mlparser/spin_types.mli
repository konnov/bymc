type var_type = TBIT | TBYTE | TSHORT
    | TINT | TUNSIGNED | TCHAN | TMTYPE ;;
type xu_type = XS | XR;;

val var_type_s:
    var_type -> string;;

val xu_type_s:
    xu_type -> string;;
