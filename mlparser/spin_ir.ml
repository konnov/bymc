(*
 * The intermediate representation of the Promela code parsed by ocamlyacc.
 *
 * Igor Konnov <konnov@forsyte.at>, 2012.
 *
 * The idea of this OCAML code was first derivated from the original
 * code of Spin 6.1.0, but since then the code has been refactored a
 * lot to fit into the OCAML concepts.
 *)

open Spin_types;;

type btype = BNone | NClaim | IProc | AProc | PProc | ETrace | NTrace;;
type hflag = HNone | HHide | HShow | HBitEquiv | HByteEquiv
           | HFormalPar | HInlinePar | HTreatLocal | HReadOnce;;

(*

 Spin-like types, too complicated

(* 't stands for the token type *)
type 't lextok = {
    ntyp: 't;                   (* node type *)
    mutable nval: int;          (* a value attached to the node *)
    (* line number and filename are omitted *)
    mutable sym: 't zsymbol;    (* the symbol reference *)
    mutable subtree: 't lextok_tree; (* children *)
}
and 't lextok_tree =
    Lextok_leaf
  | Lextok_list of 't lextok
  | Lextok_tree of 't lextok * 't lextok
and 't access = {
    who: 't zsymbol;    (* proctype name of accessor *)
    what: 't zsymbol;   (* proctype name of accessed *)
    cnt: int;       (* parameter nr *)
    typ: int;       (* and, e.g., 's' or 'r' *)
}
and
(* a symbol produced by the parser *)
't symbol = {
    mutable name: string;
    mutable nid: int;
    mutable hidden: hflag list;
    mutable isarray: bool;      (* set if decl specifies array bound *)
    mutable bscp: int;          (* block scope *)
    mutable nbits: int;         (* optional width specifier *)
    mutable nel: int;           (* 1 if scalar, >1 if array *)
    mutable setat: int;         (* last depth value changed *)
    mutable rval: int list;     (* runtime value(s) *)
    mutable sval: 't list;      (* values for structures *)
    mutable xu: int;            (* exclusive r or w by 1 pid *)
    mutable xup: 't zsymbol list; (* xr or xs prototype *)
    mutable access: 't access list; (* e.g., senders and receivers of chan *)
    mutable ini: 't;            (* initial value, or chan-def *)
    mutable slst: 't;           (* template for structure if struct *)
    mutable snm: 't zsymbol;     (* name of the defining struct *)
    mutable owner: 't zsymbol;   (* set for names of subfields in typedefs *)
    mutable context: 't zsymbol; (* 0 if global, or procname *)
    (* next: symbol; /* linked list */ *)
}
and 't zsymbol = Symb of 't symbol | ZSymb;;

type 't element = {
    mutable n: 't;              (* defines the type & contents *)
    mutable sseqno: int;        (* identifies this el within system *)
    mutable pseqno: int;        (* identifies this el within a proc *)
    mutable merge:  int;        (* set by -O if step can be merged  *)
    mutable merge_start: int;
    mutable merge_single: int;
    mutable merge_in: int;      (* nr of incoming edges *)
    mutable merge_mark: int;    (* state was generated in merge sequence *)
    mutable status: int;        (* used by analyzer generator *)
	(* struct FSM_use	*dead;	/* optional dead variable list */ *)
	sub: 't element list list;	(* subsequences, for compounds *)
	esc: 't element list list;	(* zero or more escape sequences *)
	(* struct Element	*Nxt;	/* linked list - for global lookup */
	struct Element	*nxt;	/* linked list - program structure */ *)
};;

type 't zelement = Elem of 't element | ZElem;;

type 't process = {
    mutable name: 't zsymbol;
    mutable params: 't list;
    mutable seq: 't element list;   (* body *)
    mutable prov: 't list;          (* provided clause *)
    mutable b: btype;               (* e.g., claim, trace, proc *)
    mutable tn: int;                (* ordinal number *)
    mutable det: int;               (* deterministic *)
    mutable unsafe: int;            (* contains global var inits *)
};;
*)

exception Invalid_type of string;;

(* a symbol of any origin *)
class symb name_i =
    object(self)
        val name: string = name_i
        val mutable flags: hflag list = [] (* 'hidden' in Spin *)

        method get_name = name

        method has_flag f = List.mem f flags

        method add_flag f =
            flags <-
                if f != HNone && self#has_flag f
                then flags
                else f::flags

        (* is there a better way to do this? *)
        method as_var: unit -> var =
            raise (Invalid_type "symb is not var")
    end
and
(* a variable, not a generalized symbol *)
var name_i =
    object(self)
        inherit symb name_i

        val mutable vtype = TINT
        val mutable isarray: bool = false (* set if decl specifies array bound *)
        val mutable nbits: int = 0        (* optional width specifier *)
        val mutable nel: int = 1          (* 1 if scalar, >1 if array *)
        val mutable ini: int = 0          (* initial value, or chan-def *)
        
        method as_var () = (self :> var)

        method set_type t = vtype <- t
        method get_type = vtype

        method set_isarray b = isarray <- b
        method get_isarray = isarray

        method set_nbits n = nbits <- n
        method get_nbits = nbits

        method set_num_elems n = nel <- n
        method get_num_elems = nel

        method set_ini i = ini <- i
        method get_ini = ini
    end
;;

exception Symbol_not_found of string;;

(* a symbol table *)
class symb_tab =
    object(self)
        val tab: (string, symb) Hashtbl.t = Hashtbl.create 10
        val mutable parent: symb_tab option = None

        method add_symb name symb = Hashtbl.add tab name symb
        method lookup name =
            try
                Hashtbl.find tab name
            with Not_found ->
                match parent with
                | None -> (* XXX: show the position in the file! *)
                    raise (Symbol_not_found
                        (Printf.sprintf "Variable %s is not declared" name))
                | Some p -> p#lookup name

        method set_parent p = parent <- Some p
        method get_parent = parent
    end
;;


type 't expr = Nop | Const of int | Var of var
    | UnEx of 't * 't expr | BinEx of 't * 't expr * 't expr
;;

type 't stmt = Skip | Expr of 't expr
    | Decl of var * 't expr
    | Label of int
    | Atomic_beg | Atomic_end | D_step_beg | D_step_end
    | Goto of int | Goto_unresolved of string
    | If of int list | Else
    | Assert of 't expr | Assume of 't expr
    | Print of string * 't expr list
;;

(* a process *)
class ['t] proc name_i =
    object
        inherit symb name_i
        inherit symb_tab

        val mutable stmts: 't stmt list = []

        method set_stmts s = stmts <- s
        method get_stmts = stmts
    end
;;

type 't prog_unit = Proc of 't proc | Stmt of 't stmt | None;;

