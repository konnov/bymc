(**
 * The intermediate representation of the Promela code parsed by ocamlyacc.
 *
 * @author Igor Konnov <konnov@forsyte.at>, 2012-2014.
 *
 * The idea of this OCAML code was first derivated from the original
 * code of Spin 6.1.0, but since then the code has been refactored a
 * lot to fit into the OCAML concepts. We further refactored the code to
 * support several layers of code transformations.
 *)

exception Invalid_type of string
exception Symbol_not_found of string
exception Type_not_found of string

(** Symbol types *)
type sym_type = SymGen | SymVar | SymLab

(** Annotation types *)
type annot_t = AnnotBefore of string | AnnotAfter of string

(** Flags as in Promela (are they used anywhere? *)
type btype = BNone | NClaim | IProc | AProc | PProc | ETrace | NTrace

(** Variable flags *)
type hflag = HNone | HHide | HShow | HBitEquiv | HByteEquiv
           | HFormalPar | HInlinePar | HTreatLocal | HReadOnce
           (* our extensions *)
           | HSymbolic | HInstrumental

(** A symbol of any origin, e.g., a variable, a label, etc. *)
class symb: string ->
    object
        (** @return symbol type *)
        method get_sym_type: sym_type

        (** @return symbol name *)
        method get_name: string

        (** Check, whether the symbol is marked with a flag.
            @return true when it is marked
         *)
        method has_flag: hflag -> bool

        (** Mark symbol with a flag *)
        method add_flag: hflag -> unit

        (** Get all flags the symbol is marked with *)
        method get_flags: hflag list

        (** Set all flags *)
        method set_flags: hflag list -> unit

        (** Get a textual representation of flags *)
        method flags_s: string

        (** Try to convert this symbol to a variable
            @return object of class var
            @raise Invalid_type when the symbol cannot be coerced
         *)
        method as_var: var

        (** Try to convert this symbol to a label
            @return object of class label
            @raise Invalid_type when the symbol cannot be coerced
         *)
        method as_label: label
    end
and
(** A variable, not a generalized symbol.
   Every variable has an identifier associated with it.
 *)
    var: string -> int ->
    object 
        inherit symb

        (** @return variable's unique identifier *)
        method id: int

        (** Whether the variable is marked as symbolic *)
        method is_symbolic: bool

        (** Mark the variable as symbolic *)
        method set_symbolic: unit

        (** Whether the variable is marked as instrumental *)
        method is_instrumental: bool

        (** Mark the variable as instrumental *)
        method set_instrumental: unit

        (** Get the name of the owning process *)
        method proc_name: string

        (** Set the name of the owning process *)
        method set_proc_name: string -> unit

        (** Get the index of the owning process *)
        method proc_index: int

        (** Set the index of the owning process *)
        method set_proc_index: int -> unit

        (** Get the mark of the variable (useful in search algorithms) *)
        method mark: int

        (** Set the mark (useful in search algorithms) *)
        method set_mark: int -> unit

        (** Return the qualified name including the process name and   
            the process index, if available
        *)
        method qual_name: string

        (** Return the qualified name without special characters *)
        method mangled_name: string

        (** Make a copy of the variable with new name
            but old identifier
        *)
        method copy: string -> var

        (** Make a copy of the variable with new name
            and new identifier
        *)
        method fresh_copy: string -> var
    end
and
(** A label that is mapped to an integer. *)
    label: string -> int ->
    object 
        inherit symb

        method get_name : string

        (** @return symbol type, i.e., SymLab *)
        method get_sym_type: sym_type

        (** Try to convert this symbol to a label
            @return object of class label
            @raise Invalid_type when the symbol cannot be coerced
         *)
        method as_label: label

        (** Get the number attached to the label *)
        method get_num: int
    end


(** Symbol table *)
class symb_tab: string ->
    object
        method tab_name: string

        method add_symb: string -> symb -> unit

        method add_all_symb: symb list -> unit

        method set_syms: symb list -> unit

        (** Find a symbol with the given name either in the table,
            or in its parents.
            @param name symbol's name
            @return symbol, if found
            @raise Symbol_not_found, when there is no symbol
            *)
        method lookup: string -> symb

        (** Find a symbol with the given name without looking in
            the parents' tables
            @param name symbol's name
            @return symbol, if found
            @raise Not_found, when there is no symbol
            *)
        method find_or_error: string -> symb

        method get_symb_pairs: (string * symb) list

        method get_symb_pairs_rec: (string * symb) list

        method get_symbs: symb list

        method get_symbs_rec: symb list

        method set_parent: symb_tab -> unit

        method set_parent_opt: symb_tab option -> unit

        method get_parent: symb_tab option
    end

(** Variable data type *)
class data_type :
  SpinTypes.var_type ->
  object
    val m_basetype : SpinTypes.var_type
    val mutable m_isarray : bool
    val mutable m_nbits : int
    val mutable m_nelems : int
    val mutable m_range : int * int
    method basetype : SpinTypes.var_type
    method copy : data_type
    method has_range : bool
    method is_array : bool
    method nbits : int
    method nelems : int
    method range : int * int
    method range_len : int
    method range_list : int list
    method set_nbits : int -> unit
    method set_nelems : int -> unit
    method set_range : int -> int -> unit
    method set_range_tuple : int * int -> unit
    method to_s : string
  end

class data_type_tab :
  object
    val mutable m_tab : (int, data_type) Hashtbl.t
    method copy : data_type_tab
    method get_type : var -> data_type
    method has_type : var -> bool
    method length : int
    method print : unit
    method set_all_types : (int, data_type) Hashtbl.t -> unit
    method set_type : var -> data_type -> unit
  end


type 't expr =
    Nop of string
  | IntConst of int
  | Var of var
  | UnEx of 't * 't expr
  | BinEx of 't * 't expr * 't expr
  | Phi of var * var list
  | LabelRef of string * string
  

type 't stmt =
    Skip of int
  | Expr of int * 't expr
  | Decl of int * var * 't expr
  | Label of int * int
  | Atomic_beg of int
  | Atomic_end of int
  | D_step_beg of int
  | D_step_end of int
  | Goto of int * int
  | If of int * int list
  | Assert of int * 't expr
  | Assume of int * 't expr
  | Havoc of int * var
  | Print of int * string * 't expr list


type 't mir_stmt =
    MSkip of int
  | MExpr of int * 't expr
  | MDecl of int * var * 't expr
  | MLabel of int * string
  | MAtomic of int * 't mir_stmt list
  | MD_step of int * 't mir_stmt list
  | MGoto of int * string
  | MIf of int * 't mir_option list
  | MAssert of int * 't expr
  | MAssume of int * 't expr
  | MPrint of int * string * 't expr list
  | MHavoc of int * var
  | MUnsafe of int * string
  | MDeclProp of int * var * 't atomic_expr
and 't atomic_expr =
    PropAll of 't expr
  | PropSome of 't expr
  | PropGlob of 't expr
  | PropAnd of 't atomic_expr * 't atomic_expr
  | PropOr of 't atomic_expr * 't atomic_expr
and 't mir_option =
    MOptGuarded of 't mir_stmt list
  | MOptElse of 't mir_stmt list


(** A process prototype (similar to a process in Promela).
    Every process is a symbolic table.
 *)
class ['t] proc :
  string ->
  't expr ->
  object
    val mutable flags : hflag list
    val mutable m_active_expr : 't expr
    val mutable m_args : var list
    val mutable m_provided_expr : 't expr
    val mutable m_stmts : 't mir_stmt list
    val name : string
    val mutable parent : symb_tab option
    val mutable tab : (string, symb) Hashtbl.t
    method add_all_symb : symb list -> unit
    method add_flag : hflag -> unit
    method add_symb : string -> symb -> unit
    method as_label : label
    method as_var : var
    method copy : string -> 't proc
    method find_or_error : string -> symb
    method flags_s : string
    method get_active_expr : 't expr
    method get_args : var list
    method get_flags : hflag list
    method get_locals : var list
    method get_name : string
    method get_parent : symb_tab option
    method get_provided : 't expr
    method get_stmts : 't mir_stmt list
    method get_sym_type : sym_type
    method get_symb_pairs : (string * symb) list
    method get_symb_pairs_rec : (string * symb) list
    method get_symbs : symb list
    method get_symbs_rec : symb list
    method has_flag : hflag -> bool
    method labels_as_hash : (string, label) Hashtbl.t
    method lookup : string -> symb
    method set_active_expr : 't expr -> unit
    method set_args : var list -> unit
    method set_flags : hflag list -> unit
    method set_parent : symb_tab -> unit
    method set_parent_opt : symb_tab option -> unit
    method set_provided : 't expr -> unit
    method set_stmts : 't mir_stmt list -> unit
    method set_syms : symb list -> unit
    method tab_name : string
  end


type 't prog_unit =
    Proc of 't proc
  | Stmt of 't mir_stmt
  | Ltl of string * 't expr
  | EmptyUnit



module VarSet: (Set.S with type elt = var)

(*************************** GENERAL FUNCTIONS ********************)

(** generate a unique identifier, limited by MAX_INT *)
val fresh_id: unit -> int

(** create a unique label *)
val mk_uniq_label: unit -> int

(** create a new variable with a fresh identifier *)
val new_var: string -> var

(** @return variable's qualified name *)
val var_qname: var -> string
(** @return variable's name *)
val var_name: var -> string


val mk_int_range : int -> int -> data_type

(*************************** EXPRESSIONS ********************)
val is_nop : 'a expr -> bool
val not_nop : 'a expr -> bool
val is_c_true : 'a expr -> bool
val is_c_false : 'a expr -> bool
val is_var : 'a expr -> bool
val cmp_vars : var -> var -> int
val cmp_qual_vars : var -> var -> int
val expr_used_vars : 't expr -> var list
val expr_list_used_vars : 't expr list -> var list
val expr_exists : ('a expr -> bool) -> 'a expr -> bool
val not_symbolic : 'a expr -> bool
val is_symbolic : 'a expr -> bool
val expr_forall : ('a expr -> bool) -> 'a expr -> bool

(*************************** STATEMENTS ********************)
val stmt_id : 'a stmt -> int
val is_expr : 'a stmt -> bool
val expr_of_stmt : 'a stmt -> 'a expr
val cmp_stmt : 'a stmt -> 'b stmt -> int
val replace_stmt_id : int -> 'a stmt -> 'a stmt

val m_stmt_id : 'a mir_stmt -> int
val mk_comment : string -> 'a mir_stmt
val fresh_m_stmt : 'a mir_stmt -> 'a mir_stmt
val cmp_m_stmt : 'a mir_stmt -> 'b mir_stmt -> int
val expr_of_m_stmt : 'a mir_stmt -> 'a expr
val is_decl : 'a stmt -> bool
val is_mdecl : 'a mir_stmt -> bool
val stmt_list_used_vars : 't stmt list -> var list

(************************** PROCESSES AND UNITS ******************)
val proc_replace_body : 't proc -> 't mir_stmt list -> 't proc

val map_vars : (var -> 'a expr) -> 'a expr -> 'a expr

val proc_of_unit : 'a prog_unit -> 'a proc

val list_to_binex : 'a -> 'a expr list -> 'a expr

val sub_basic_stmt :
  ('a mir_stmt -> 'a mir_stmt) -> 'a mir_stmt -> 'a mir_stmt

val sub_basic_stmt_with_list :
  ('a mir_stmt -> 'a mir_stmt list) -> 'a mir_stmt list -> 'a mir_stmt list

val sub_stmt_with_list :
  ('t mir_stmt -> bool * 't mir_stmt list) ->
  't mir_stmt list -> 't mir_stmt list

val map_expr_in_stmt : ('a expr -> 'a expr) -> 'a mir_stmt -> 'a mir_stmt

val map_expr_in_lir_stmt : ('a expr -> 'a expr) -> 'a stmt -> 'a stmt

(************************** MISC FUNCTIONS ******************)

(** Flag to string *)
val hflag_s: hflag -> string

(** Marshal the internal data structures *)
val save_internal_globals: out_channel -> unit

(** Unmarshal the internal data structures *)
val load_internal_globals: in_channel -> unit

