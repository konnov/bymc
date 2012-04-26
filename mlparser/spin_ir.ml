(*
 * The intermediate representation of the Promela code parsed by yacc.
 *
 * The code is translated into OCAML by Igor Konnov, 2012.
 *
 * This OCAML code is derivated from the original code of Spin 6.1.0
 * distributed on the following conditions:

/* Copyright (c) 1989-2009 by Lucent Technologies, Bell Laboratories.     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* No guarantee whatsoever is expressed or implied by the distribution of */
/* this code.  Permission is given to distribute this code provided that  */
/* this introductory message is not removed and no monies are exchanged.  */
/* Software written by Gerard J. Holzmann.  For tool documentation see:   */
/*             http://spinroot.com/                                       */
/* Send all bug-reports and/or questions to: bugs@spinroot.com            */
 *)

open Spin_types;;

type btype = BNone | NClaim | IProc | AProc | PProc | ETrace | NTrace;;
type hflag = HHide | HShow | HBitEquiv | HByteEquiv | HFormalPar
           | HInlinePar | HTreatLocal | HReadOnce;;

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

(* a symbol of any origin *)
class symb name_i =
    object(self)
        val name: string = name_i
        val mutable flags: hflag list = [] (* 'hidden' in Spin *)

        method has_flag f = List.mem f flags

        method add_flag f =
            flags <- if self#has_flag f then flags else f::flags
    end
;;

exception Symbol_not_found of string;;

(* a symbol table *)
class symb_tab =
    object
        val tab: (string, symb) Hashtbl.t = Hashtbl.create 10

        method add_symb name symb = Hashtbl.add tab name symb
        method lookup name =
            try
                Hashtbl.find tab name
            with Not_found ->
                (* XXX: show the position in the file! *)
                raise (Symbol_not_found
                    (Printf.sprintf "The variable %s is not declared" name))
    end
;;

(* a process *)
class proc name_i =
    object
        inherit symb name_i
        inherit symb_tab
    end
;;

(* a constant value *)
class immediate v_i =
    object
        val v: int = v_i
    end
;;


(* a variable, not a generalized symbol *)
class var name_i =
    object
        inherit symb name_i

        val isarray: bool = false (* set if decl specifies array bound *)
        val nbits: int = 0        (* optional width specifier *)
        val nel: int = 1          (* 1 if scalar, >1 if array *)
        val ini: int = 0          (* initial value, or chan-def *)
    end
;;


type 't expr = Const of immediate | Var of var
    | UnEx of 't * 't expr | BinEx of 't * 't expr * 't expr;;

