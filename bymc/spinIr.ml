(*
 * The intermediate representation of the Promela code parsed by ocamlyacc.
 *
 * Igor Konnov <konnov@forsyte.at>, 2012.
 *
 * The idea of this OCAML code was first derivated from the original
 * code of Spin 6.1.0, but since then the code has been refactored a
 * lot to fit into the OCAML concepts.
 *)

open SpinTypes;;

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

exception Invalid_type of string;;

type sym_type = SymGen | SymVar | SymLab;;

(* a symbol of any origin *)
class symb name_i =
    object(self)
        val name: string = name_i
        val mutable flags: hflag list = [] (* 'hidden' in Spin *)

        method get_sym_type = SymGen

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

        (* is there a better way to do this? *)
        method as_label =
            raise (Invalid_type "symb is not label")
    end
and
(* a variable, not a generalized symbol *)
var name_i =
    object(self)
        inherit symb name_i

        val mutable vtype = TINT
        val mutable m_isarray: bool = false (* set if decl specifies array bound *)
        val mutable nbits: int = 0        (* optional width specifier *)
        val mutable nel: int = 1          (* 1 if scalar, >1 if array *)
        val mutable ini: int = 0          (* initial value, or chan-def *)

        (* a forward reference to a context (a process) that has not been
           defined yet *)
        val mutable m_proc_name: string = "" 
        val mutable m_proc_index: int = -1

        method get_sym_type = SymVar
        
        method as_var = (self :> var)

        method set_type t = vtype <- t
        method get_type = vtype

        method set_isarray b = m_isarray <- b
        method is_array = m_isarray

        method set_nbits n = nbits <- n
        method get_nbits = nbits

        method set_num_elems n = nel <- n
        method get_num_elems = nel

        method set_ini i = ini <- i
        method get_ini = ini

        method is_symbolic = self#has_flag HSymbolic
        method set_symbolic = self#add_flag HSymbolic

        method proc_name = m_proc_name
        method set_proc_name r = m_proc_name <- r

        method proc_index = m_proc_index
        method set_proc_index i = m_proc_index <- i

        method copy new_name =
            let new_var = new var new_name in
            new_var#set_type vtype;
            new_var#set_isarray m_isarray;
            new_var#set_nbits nbits;
            new_var#set_num_elems nel;
            new_var#set_ini ini;
            if self#is_symbolic then new_var#set_symbolic;
            new_var#set_proc_name m_proc_name;
            new_var#set_proc_index m_proc_index;
            new_var
    end
and
(* a label mapped to an integer *)
label name_i num_i =
    object(self)
        inherit symb name_i

        val mutable num: int = num_i

        method get_sym_type = SymLab
        
        method as_label = (self :> label)

        method get_num = num
    end
;;

exception Symbol_not_found of string;;

(* a symbol table *)
class symb_tab =
    object(self)
        val tab: (string, symb) Hashtbl.t = Hashtbl.create 10
        val mutable parent: symb_tab option = None

        method add_symb name symb = Hashtbl.add tab name symb
        method add_all_symb symb_list =
            List.iter (fun s -> Hashtbl.add tab s#get_name s) symb_list

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

        method get_symbs = Accums.hashtbl_as_list tab

        method set_parent p = parent <- Some p
        method get_parent = parent
    end
;;

type 't expr = Nop of string (* a comment *) | Const of int | Var of var
    | UnEx of 't * 't expr | BinEx of 't * 't expr * 't expr
    | Phi of var * var list (* a phi function for SSA purposes *)
    | LabelRef of string * string (* a reference to a process label *)
;;

let is_nop = function
    | Nop _ -> true
    | _ -> false
;;

let not_nop e = not (is_nop e);; (* a shorthand *)

let is_var = function
    | Var _ -> true
    | _ -> false
;;

let cmp_vars vx vy =
    String.compare vx#get_name vy#get_name;;

let expr_used_vars (expression: 't expr) : var list =
    let rec find_used e =
        match e with
        | Var v -> if v#is_symbolic then [] else [v]
        | UnEx (_, f) -> find_used f
        | BinEx (_, f, g) -> List.append (find_used f) (find_used g)
        | _ -> []
    in
    Accums.list_sort_uniq cmp_vars (find_used expression)
;;

let expr_list_used_vars (exprs: 't expr list) : var list =
    (* by using hashtbl we avoid duplicate elements *)
    let tbl = Hashtbl.create 10 in
    let collect_for_expr e =
        let vs = expr_used_vars e in
        List.iter (fun v -> Hashtbl.replace tbl v#get_name v) vs
    in
    List.iter collect_for_expr exprs;
    List.sort cmp_vars (Accums.hashtbl_vals tbl)
;;

let rec expr_exists func e =
    if (func e)
    then true
    else match e with
    | UnEx (_, f) -> expr_exists func f
    | BinEx (_, f, g) -> (expr_exists func f) || (expr_exists func g)
    | _ -> false
;;

let rec expr_forall func e = not (expr_exists (fun f -> not (func f)) e) ;;

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
    | Assert of int * 't expr
    | Assume of int * 't expr
    | Havoc of int * var (* forget about the current value of the variable *)
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
    | Assert (id, _) -> id
    | Assume (id, _) -> id
    | Havoc (id, _) -> id
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
    | Assert (_, e) -> Assert (new_id, e)
    | Assume (_, e) -> Assume (new_id, e)
    | Havoc (_, v) -> Havoc (new_id, v)
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
    | MHavoc of int * var
    | MUnsafe of int * string (* a statement never interpreted but copied*)
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
    | MHavoc (id, _) -> id
    | MUnsafe (id, _) -> id
    | MDeclProp (id, _, _) -> id
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
    object(self)
        inherit symb name_i
        inherit symb_tab

        val mutable args: var list = []
        val mutable stmts: 't mir_stmt list = []
        (* a symbolic expression *)
        val mutable active_expr: 't expr = active_expr_i
        (* a provided clause if any *)
        val mutable provided_expr: 't expr = Nop ""

        method set_args a = args <- a
        method get_args = args

        method set_stmts s = stmts <- s
        method get_stmts = stmts

        method set_active_expr e = active_expr <- e
        method get_active_expr = active_expr

        method set_provided e = provided_expr <- e
        method get_provided = provided_expr

        method labels_as_hash =
            let symbs = List.filter
                (fun (_, s) -> SymLab = s#get_sym_type)
                self#get_symbs in
            let tbl = Hashtbl.create (List.length symbs) in
            List.iter
                (fun (_, s) ->
                    Hashtbl.add tbl s#get_name s#as_label)
                symbs;
            tbl

        method get_locals =
            let add_decl l = function
                | MDecl (_, v, _) -> v :: l
                | _ -> l
            in
            List.fold_left add_decl [] stmts
    end
;;

let proc_replace_body (p: 't proc) (new_body: 't mir_stmt list) =
    let new_p = new proc p#get_name p#get_active_expr in
    new_p#set_args p#get_args;
    new_p#set_stmts new_body;
    (new_p :> symb_tab)#add_all_symb (List.map (fun (_, s) -> s) p#get_symbs);
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

type 't prog_unit = Proc of 't proc | Stmt of 't mir_stmt
    | Ltl of string * 't expr | None
;;

let proc_of_unit = function
    | Proc p -> p
    | _ -> raise (Failure "Expected Proc p, found other unit")
;;

let collect_final_labs (stmts: 't mir_stmt list)
        : ('t mir_stmt list * 't mir_stmt list) =
    let rec collect = function
    | MLabel (_, _) as s :: tl ->
        let ls, os = collect tl in
        (s :: ls, os)
    | _ as lst ->
        ([], lst)
    in
    let ls, os = collect (List.rev stmts) in
    (List.rev os, List.rev ls)
;;

(* convert a list of expressions [e1, ..., ek] to a binary tree
   (tok, e1, (tok, e2, (... (tok, e(k-1), ek) ...))).
   Nop expressions are ignored.
 *)
let list_to_binex tok lst =
    let join_e ae e =
        if not (is_nop e)
        then if not (is_nop ae) then BinEx (tok, ae, e) else e
        else ae
    in
    List.fold_left join_e (Nop "") lst
;;

