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

module StringSet = Set.Make(String);;

(* here we use a global variable to generate unique variables everywhere *)
let label_next = ref 1;;

let mk_uniq_label () =
    let n = !label_next in
        label_next := (n + 1); n
;;

type btype = BNone | NClaim | IProc | AProc | PProc | ETrace | NTrace;;
type hflag = HNone | HHide | HShow | HBitEquiv | HByteEquiv
           | HFormalPar | HInlinePar | HTreatLocal | HReadOnce
           (* our extensions *)
           | HSymbolic ;;

let hflag_s f =
    match f with
    | HHide -> ":hide:"
    | HShow -> ":show:"
    | HBitEquiv -> ":biteq:"
    | HByteEquiv -> ":byteeq:"
    | HFormalPar -> ":formalpar:"
    | HInlinePar -> ":inlinepar:"
    | HTreatLocal -> ":local:"
    | HReadOnce -> ":readonce:"
    | HSymbolic -> ":symbolic:"
    | HNone -> ""
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
                if f == HNone || self#has_flag f
                then flags
                else f :: flags

        method get_flags = flags
        
        method flags_s =
            List.fold_left
                (fun a f -> (if a <> "" then a^ " " else "") ^ (hflag_s f))
                "" flags

        (* is there a better way to do this? *)
        method as_var =
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
        
        method as_var = (self :> var)

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

        method is_symbolic = self#has_flag HSymbolic
        method set_symbolic = self#add_flag HSymbolic
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

        method find_or_error name = Hashtbl.find tab name

        method set_parent p = parent <- Some p
        method get_parent = parent
    end
;;

type 't expr = Nop | Const of int | Var of var
    | UnEx of 't * 't expr | BinEx of 't * 't expr * 't expr
;;

let is_var = function
    | Var _ -> true
    | _ -> false
;;

let expr_used_vars (expression: 't expr) : var list =
    let rec find_used e =
        match e with
        | Var v -> if v#is_symbolic then [] else [v]
        | UnEx (_, f) -> find_used f
        | BinEx (_, f, g) -> List.append (find_used f) (find_used g)
        | _ -> []
    in
    let used = (List.fast_sort
        (fun vx vy ->
            String.compare vx#get_name vy#get_name) (find_used expression)) in
    (* remove duplicates, one could have used BatList.sort_unique *)
    match used with
    | [] -> []
    | [hd] -> [hd]
    | hd :: tl ->
            hd :: (List.fold_left2
                (fun l cur prev -> if cur <> prev then cur :: l else l)
                []
                tl
                (hd :: (List.rev (List.tl (List.rev tl)))))
;;

let rec expr_exists func e =
    if (func e)
    then true
    else match e with
    | UnEx (_, f) -> expr_exists func f
    | BinEx (_, f, g) -> (expr_exists func f) || (expr_exists func g)
    | _ -> false
;;

(*
 A low-level statement, no block structure preserved.
 The first field is always the identifier of a statement.
 Negative identifiers label auxillary statements added during the translation
 from MIR to LIR.
 *)
type 't stmt =
      Skip of int
    | Expr of int * 't expr
    | Decl of int * var * 't expr
    | Label of int * int
    | Atomic_beg of int | Atomic_end of int
    | D_step_beg of int | D_step_end of int
    | Goto of int * int
    | If of int * int list (* condition labels *) * int (* exit label *)
    | Else of int
    | Assert of int * 't expr | Assume of int * 't expr
    | Print of int * string * 't expr list
;;

let stmt_id = function
      Skip id -> id
    | Expr (id, _) -> id
    | Decl (id, _, _) -> id
    | Label (id, _) -> id
    | Atomic_beg id -> id
    | Atomic_end id -> id
    | D_step_beg id -> id
    | D_step_end id -> id
    | Goto (id, _) -> id
    | If (id, _, _) -> id
    | Else id -> id
    | Assert (id, _) -> id
    | Assume (id, _) -> id
    | Print (id, _, _) -> id
;;

let replace_stmt_id new_id = function
      Skip _ -> Skip new_id
    | Expr (_, e) -> Expr (new_id, e)
    | Decl (_, v, e) -> Decl (new_id, v, e)
    | Label (_, l) -> Label (new_id, l)
    | Atomic_beg _ -> Atomic_beg new_id
    | Atomic_end _ -> Atomic_end new_id
    | D_step_beg _ -> D_step_beg new_id
    | D_step_end _ -> D_step_end new_id
    | Goto (_, l) -> Goto (new_id, l)
    | If (_, opt_labs, exit_lab) -> If (new_id, opt_labs, exit_lab)
    | Else _ -> Else new_id
    | Assert (_, e) -> Assert (new_id, e)
    | Assume (_, e) -> Assume (new_id, e)
    | Print (_, f, a) -> Print (new_id, f, a)
;;

(* A middle-level statement, the block structure is still in place.
   Each statement has an identifier attached.
 *)
type 't mir_stmt =
      MSkip of int | MExpr of int * 't expr
    | MDecl of int * var * 't expr
    | MLabel of int * int
    | MAtomic of int * 't mir_stmt list | MD_step of int * 't mir_stmt list
    | MGoto of int * int
    | MIf of int * 't mir_option list
    | MAssert of int * 't expr
    | MAssume of int * 't expr
    | MPrint of int * string * 't expr list
    | MDeclProp of int * var * 't atomic_expr
and 't atomic_expr =
      PropAll of 't expr
    | PropSome of 't expr
    | PropGlob of 't expr (* refers to global variables only *)
and 't mir_option =
      MOptGuarded of 't mir_stmt list
    | MOptElse of 't mir_stmt list
;;

let m_stmt_id = function
      MSkip id -> id
    | MExpr (id, _) -> id
    | MDecl (id, _, _) -> id
    | MLabel (id, _) -> id
    | MAtomic (id, _) -> id
    | MD_step (id, _) -> id
    | MGoto (id, _) -> id
    | MIf (id, _) -> id
    | MAssert (id, _) -> id
    | MAssume (id, _) -> id
    | MPrint (id, _, _) -> id
;;

let mir_to_lir (stmts: 't mir_stmt list) : 't stmt list =
    let rec make_one s tl =
        match s with
        | MIf (id, options) ->
            let exit_lab = mk_uniq_label () in
            let labs_seqs = List.map (make_option exit_lab) options in
            let opt_labs, opt_seqs = List.split labs_seqs in
            If (id, opt_labs, exit_lab)
                :: ((List.concat opt_seqs) @ (Label (-1, exit_lab) :: tl))
        | MAtomic (id, seq) ->
            let new_seq = List.fold_right make_one seq [] in
            Atomic_beg id :: new_seq @ Atomic_end (-1) :: tl
        | MD_step (id, seq) ->
            let new_seq = List.fold_right make_one seq [] in
            D_step_beg id :: new_seq @ D_step_end (-1) :: tl
        | MGoto (id, i) -> Goto (id, i) :: tl
        | MLabel (id, i) -> Label (id, i) :: tl
        | MDecl (id, v, i) -> Decl (id, v, i) :: tl
        | MExpr (id, e) -> Expr (id, e) :: tl
        | MSkip id -> Skip id :: tl
        | MAssert (id, e) -> Assert (id, e) :: tl
        | MAssume (id, e) -> Assume (id, e) :: tl
        | MPrint (id, s, args) -> Print (id, s, args) :: tl
    and
        make_option exit_lab opt =
        let is_else, seq = match opt with
            | MOptGuarded sts -> (false, sts)
            | MOptElse sts -> (true, sts)
        in
        let opt_lab = mk_uniq_label () in
        let body = List.fold_right make_one seq [] in
        let body = if is_else then Else (-1) :: body else body in
        let new_seq = 
            ((Label (-1, opt_lab) :: body) @ [Goto (-1, exit_lab)])
        in
        (opt_lab, new_seq)
    in
    let lstmts = List.fold_right make_one stmts [] in
    (* assign unique negative ids instead of just -1's *)
    let _, res = List.fold_right
        (fun s (min_id, tl) ->
            let s_id = stmt_id s in
            if s_id = -1
            then (min_id - 1, (replace_stmt_id min_id s) :: tl)
            else (min_id, s :: tl)
        ) lstmts (-1, []) 
    in
    res
;;

(* find the first statement with a non-negative id *)
let first_normal_stmt seq =
    List.find (fun s -> (stmt_id s) >= 0) seq
;;

let is_decl = function
    | Decl (_, _, _) -> true
    | _ -> false
;;

let is_mdecl = function
    | MDecl (_, _, _) -> true
    | _ -> false
;;

(* a process *)
class ['t] proc name_i active_expr_i =
    object
        inherit symb name_i
        inherit symb_tab

        val mutable args: var list = []
        val mutable stmts: 't mir_stmt list = []
        (* a symbolic expression *)
        val mutable active_expr: 't expr = active_expr_i

        method set_args a = args <- a
        method get_args = args

        method set_stmts s = stmts <- s
        method get_stmts = stmts

        method set_active_expr e = active_expr <- e
        method get_active_expr = active_expr

        method get_locals =
            List.fold_left 
                (fun l s ->
                    match s with
                    | MDecl (_, v, _) -> v :: l
                    | _ -> l)
                []
                stmts
    end
;;

let proc_replace_body (p: 't proc) (new_body: 't mir_stmt list) =
    let new_p = new proc p#get_name p#get_active_expr in
    new_p#set_args p#get_args;
    new_p#set_stmts new_body;
    new_p
;;

let map_vars map_fun ex =
    let rec sub = function
    | Var v -> map_fun v
    | UnEx (t, l) -> UnEx (t, sub l)
    | BinEx (t, l, r) -> BinEx (t, sub l, sub r)
    | _ as e -> e
    in
    sub ex
;;

type 't prog_unit = Proc of 't proc | Stmt of 't mir_stmt | None;;

