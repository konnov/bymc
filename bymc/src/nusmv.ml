open Printf

open Accums
open Spin
open SpinIr
open SpinIrImp
open SpinTypes

exception Smv_error of string

let var_type_smv tp =
    let base_str = function
      | TBIT -> "boolean"
      | TBYTE -> "boolean"
      | TSHORT -> "integer"
      | TINT -> "integer"
      | TUNSIGNED -> raise (Smv_error "Unsigned is not supported")
      | TCHAN -> raise (Smv_error "Unsigned is not supported")
      | TMTYPE -> raise (Smv_error "Unsigned is not supported") 
      | TPROPOSITION -> raise (Smv_error "Unsigned is not supported")
      | TUNDEF -> raise (Failure "Undefined type")
    in
    let l, r = tp#range in
    if not tp#is_array && tp#has_range
    then sprintf "{ %s }" (str_join ", " (List.map string_of_int (range l r)))
    else base_str tp#basetype


let type_default_smv tp =
    match tp#basetype with
      | TBIT -> "FALSE"
      | TBYTE -> "0"
      | TSHORT -> "0"
      | TINT -> "0"
      | TUNSIGNED -> raise (Smv_error "Unsigned is not supported")
      | TCHAN -> raise (Smv_error "Unsigned is not supported")
      | TMTYPE -> raise (Smv_error "Unsigned is not supported") 
      | TPROPOSITION -> raise (Smv_error "Unsigned is not supported")
      | TUNDEF -> raise (Failure "Undefined type")


(* a subset of nusmv language *)

type case_t = (* guard *) token expr * (* values *) token expr list


type assign_t =
    | AInit of var * case_t list
    | ANext of var * case_t list


type section_t =
    | SAssign of assign_t list
    | STrans of token expr list (* the expressions are joined with & *)
    | SInit of token expr list (* the expressions are joined with & *)
    | SInvar of token expr list (* the expressions are joined with & *)
    (* normal variable, not a module *)
    | SVar of (var * data_type) list
    (* module instance *)
    | SModInst of string * string * (var list)


type top_t =
    | Module of string * (var list) * (section_t list)
    | SLtlSpec of string * token expr
    | Justice of token expr
    (* TODO: | Compassion *)


let token_s t =
    match t with
      | ASSERT -> "ASSERT"
      | PRINT -> "PRINT"
      | PRINTM -> "PRINTM"
      | C_CODE -> "C_CODE"
      | C_DECL -> "C_DECL"
      | C_EXPR -> "C_EXPR"
      | C_STATE -> "C_STATE"
      | C_TRACK -> "C_TRACK"
      | RUN -> "RUN"
      | LEN -> "LEN"
      | ENABLED -> "ENABLED"
      | EVAL -> "EVAL"
      | PC_VAL -> "PC_VAL"
      | TYPEDEF -> "TYPEDEF"
      | MTYPE -> "MTYPE"
      | INLINE -> "INLINE"
      | LABEL -> "LABEL"
      | OF -> "OF"
      | GOTO -> "GOTO"
      | BREAK -> "BREAK"
      | ELSE -> "ELSE"
      | SEMI -> "SEMI"
      | IF -> "IF"
      | FI -> "FI"
      | DO -> "DO"
      | OD -> "OD"
      | FOR -> "FOR"
      | SELECT -> "SELECT"
      | IN -> "IN"
      | SEP -> "SEP"
      | DOTDOT -> "DOTDOT"
      | ATOMIC -> "ATOMIC"
      | NON_ATOMIC -> "NON_ATOMIC"
      | D_STEP -> "D_STEP"
      | UNLESS -> "UNLESS"
      | TIMEOUT -> "TIMEOUT"
      | NONPROGRESS -> "NONPROGRESS"
      | ACTIVE -> "ACTIVE"
      | PROCTYPE -> "PROCTYPE"
      | D_PROCTYPE -> "D_PROCTYPE"
      | HIDDEN -> "HIDDEN"
      | SHOW -> "SHOW"
      | ISLOCAL -> "ISLOCAL"
      | PRIORITY -> "PRIORITY"
      | PROVIDED -> "PROVIDED"
      | FULL -> "FULL"
      | EMPTY -> "EMPTY"
      | NFULL -> "NFULL"
      | NEMPTY -> "NEMPTY"
      | CONST i -> (string_of_int i)
      | TYPE tp -> "TYPE" ^ (var_type_s tp)
      | XU tp -> (xu_type_s tp)
      | NAME s -> "NAME " ^ s
      | UNAME s -> "UNAME " ^ s
      | PNAME s -> "PNAME " ^ s
      | INAME s -> "INAME " ^ s
      | FNAME s -> "FNAME " ^ s
      | STRING s -> "STRING " ^ s
      | CLAIM -> "CLAIM"
      | TRACE -> "TRACE"
      | INIT -> "INIT"
      | LTL -> "LTL"
      | DEFINE(n, v) -> (sprintf "DEFINE %s '%s'" n v)
      | INCLUDE(filename) -> (sprintf "INCLUDE \"%s\"" filename)
      | MACRO_IF -> "MACRO_IF"
      | MACRO_IFDEF -> "MACRO_IFDEF"
      | MACRO_ELSE -> "MACRO_ELSE"
      | MACRO_ENDIF -> "MACRO_ENDIF"
      | MACRO_OTHER name -> (sprintf "#%s" name)
      | NOTRACE -> "NOTRACE"
      | NEVER -> "NEVER"
      | R_RCV -> "R_RCV"
      | RCV -> "RCV"
      | SND -> "SND"
      | O_SND -> "O_SND"
      | RPAREN -> ")"
      | LPAREN -> "("
      | RBRACE -> "]"
      | LBRACE -> "["
      | RCURLY -> "}"
      | LCURLY -> "{"
      | DOT -> "."
      | COMMA -> ","
      | COLON -> ":"
      | INCR -> "++"
      | DECR -> "--"
      | MOD -> "%"
      | DIV -> "/"
      | MINUS -> "-"
      | UMIN -> "(-)"
      | PLUS -> "+"
      | MULT -> "*"
      | ASGN -> "="
      | BITNOT -> "~"
      | BITAND -> " & "
      | BITOR -> " | "
      | BITXOR -> " | "
      | AND -> " & "
      | OR -> " | "
      | NEG -> " ! "
      | GE -> ">="
      | LE -> "<="
      | GT -> ">"
      | LT -> "<"
      | EQ -> "="
      | NE -> "!="
      | AT -> "@"
      | LSHIFT -> "<<"
      | RSHIFT -> ">>"
      | VARREF -> "VARREF"
      | ARR_ACCESS -> "ARR_ACCESS"
      | ARR_UPDATE -> "ARR_UPDATE"
      | ALWAYS -> " G "
      | EVENTUALLY -> " F "
      | UNTIL -> " U "
      | RELEASE -> " V "
      | WEAK_UNTIL -> " W "
      | NEXT -> " next" (* the unary operator next(foo) *)
      | IMPLIES -> "->"
      | EQUIV -> "<->"
      | EOF -> "EOF"
      | ASSUME -> "ASSUME"
      | SYMBOLIC -> "SYMBOLIC"
      | ALL -> "all"
      | SOME -> "some"
      | CARD -> "card"
      | POR -> "or"
      | PAND -> "and"
      | HAVOC -> "havoc"

(* we need var_fun as variables can look either x or next(x) *)
let expr_s var_fun e =
    let rec to_s = function
    | Nop comment -> sprintf "-- %s" comment
    | Const i -> string_of_int i
    | Var v -> var_fun v
    | UnEx (CARD, f) -> sprintf "card(%s)" (to_s f)
    | UnEx (tok, f) -> sprintf "(%s(%s))" (token_s tok) (to_s f)
    | BinEx (ARR_ACCESS, arr, idx) ->
            sprintf "%s[%s]" (to_s arr) (to_s idx)
    (* XXX: not well defined *)
    | BinEx (ASGN, Var arr,
                BinEx (ARR_UPDATE, BinEx (ARR_ACCESS, Var old_arr, idx), rhs))
        ->
            sprintf "%s<-%s[%s] = %s" arr#get_name
                old_arr#get_name (to_s idx) (to_s rhs)
    | BinEx (AND, f, g) -> sprintf "(%s & %s)" (to_s f) (to_s g)
    | BinEx (OR, f, g) -> sprintf "(%s | %s)" (to_s f) (to_s g)
    | BinEx (ASGN, f, g) -> sprintf "%s = %s" (to_s f) (to_s g)
    | BinEx (AT, proc, lab) ->
        (* initialized *)
        sprintf "bymc_loc = 1"
    | BinEx (tok, f, g) ->
        sprintf "(%s %s %s)" (to_s f) (token_s tok) (to_s g)
    | Phi (lhs, rhs) ->
        let rhs_s = String.concat ", " (List.map (fun v -> v#get_name) rhs)
        in
        sprintf "%s = phi(%s)" lhs#get_name rhs_s
    | LabelRef (_, _) ->
        (* initialized *)
        sprintf "bymc_loc = 1"
    in
    to_s e


let rec form_s = function
    | Const 1 -> "TRUE"
    | BinEx (AND, f, g) -> sprintf "(%s & %s)" (form_s f) (form_s g)
    | BinEx (OR, f, g) -> sprintf "(%s | %s)" (form_s f) (form_s g)
    | UnEx (ALWAYS, f) -> sprintf " G (%s)" (form_s f)
    | UnEx (EVENTUALLY, f) -> sprintf " F (%s)" (form_s f)
    | UnEx (NEXT, f) -> sprintf " X (%s)" (form_s f)
    | BinEx (UNTIL, f, g) -> sprintf " ((%s) U (%s))" (form_s f) (form_s g)
    | BinEx (EQ, f, g) ->
            let vf v = v#get_name in
            sprintf "(%s = %s)" (expr_s vf f) (expr_s vf g)
    | BinEx (NE, f, g) ->
            let vf v = v#get_name in
            sprintf "(%s != %s)" (expr_s vf f) (expr_s vf g)
    | _ as e -> expr_s (fun v -> v#get_name) e


let case_s (guard, es) =
    let vf v = v#get_name in
    sprintf "%s : { %s };"
        (expr_s vf guard)
        (str_join ", " (List.map (expr_s vf) es))


let assign_s = function
    | AInit (v, cases) ->
            sprintf " init(%s) := case\n%s esac;"
                v#get_name (str_join ";\n" (List.map case_s cases))

    | ANext (v, cases) ->
            sprintf " next(%s) :=\n  case\n%s\n  esac;"
                v#get_name (str_join "\n" (List.map case_s cases))


let section_s s =
    let vf v = v#get_name in
    match s with
    | SAssign assigns ->
            "ASSIGN\n" ^ (str_join "\n" (List.map assign_s assigns))

    | STrans es ->
            "TRANS\n" ^ (str_join "\n  & " (List.map (expr_s vf) es))

    | SInit es ->
            "INIT\n" ^ (str_join "\n  & " (List.map (expr_s vf) es))

    | SInvar es ->
            "INVAR\n" ^ (str_join "\n  & " (List.map (expr_s vf) es))

    | SVar decls ->
            let vd (v, tp) =
                sprintf "%s: %s;" v#get_name (var_type_smv tp) in
            "VAR\n " ^ (str_join "\n " (List.map vd decls))

    | SModInst (inst_name, mod_type, params) ->
            let ps = List.map (fun v -> v#get_name) params in
            sprintf " %s: %s(%s);" inst_name mod_type (str_join ", " ps)


let top_s t =
    let vf v = v#get_name in
    match t with
    | Module (mod_type, args, sections) ->
        let a_s = str_join ", " (List.map (fun v -> v#get_name) args) in
        let sects = str_join "\n" (List.map section_s sections) in
        sprintf "MODULE %s(%s)\n%s" mod_type a_s sects

    | SLtlSpec (name, e) ->
        sprintf "LTLSPEC NAME %s := (%s);" name (form_s e)

    | Justice e ->
        sprintf "JUSTICE (%s);" (expr_s vf e)


let keep vars =
    let keep_var v =
        sprintf "(next(%s) = %s)" v#mangled_name v#mangled_name in
    str_join " & " (List.map keep_var vars)

let nostuttering vars =
    let change_var v =
        sprintf "(next(%s) != %s)" v#mangled_name v#mangled_name in
    str_join " | " (List.map change_var vars)

