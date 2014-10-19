(*
 * The intermediate representation of the Promela code parsed by ocamlyacc.
 *
 * Igor Konnov <konnov@forsyte.at>, 2012.
 *
 * The idea of this OCAML code was first derivated from the original
 * code of Spin 6.1.0, but since then the code has been refactored a
 * lot to fit into the OCAML concepts. We further refactored the code to
 * support several layers of code transformations.
 *)

open Printf
open SpinTypes


(* here we use a global variable to generate unique variables everywhere *)
let label_next = ref 1

let mk_uniq_label () =
    let n = !label_next in
        label_next := (n + 1); n


type btype = BNone | NClaim | IProc | AProc | PProc | ETrace | NTrace
type hflag = HNone | HHide | HShow | HBitEquiv | HByteEquiv
           | HFormalPar | HInlinePar | HTreatLocal | HReadOnce
           (* our extensions *)
           | HSymbolic | HInstrumental

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
    | HInstrumental -> ":instrumental:"
    | HNone -> ""

exception Invalid_type of string

type sym_type = SymGen | SymVar | SymLab

type annot_t = AnnotBefore of string | AnnotAfter of string

(* the next identifier (used for vars, statements, etc.) *)
let uniq_id_next = ref 0

(* get a new unique id *)
let fresh_id () =
    let id = !uniq_id_next in
    uniq_id_next := !uniq_id_next + 1;
    if !uniq_id_next >= 0
    then id
    else raise (Failure "fresh_id: ran out of unique identifiers")


let save_internal_globals cout =
    (* save the id *)
    Marshal.to_channel cout !uniq_id_next []


let load_internal_globals cin =
    (* restore the id *)
    let (seq_id: int) = Marshal.from_channel cin in
    uniq_id_next := seq_id




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

        method set_flags fs = flags <- fs
        
        method flags_s =
            List.fold_left
                (fun a f -> (if a <> "" then a^ " " else "") ^ (hflag_s f))
                "" flags

        (* is there a better way to do this? *)
        method as_var =
            raise (Invalid_type (sprintf "symb %s is not a var" name))

        (* is there a better way to do this? *)
        method as_label =
            raise (Invalid_type (sprintf "symb %s is not a label" name))
    end
and
(* A variable, not a generalized symbol.
   Every variable has an identifier associated with it.
 *)
var name_i var_id =
    object(self)
        inherit symb name_i

        (* the name of the owning process type (if there is one) *)
        val mutable m_proc_name: string = "" 
        (* the index of the owner process (if known) *)
        val mutable m_proc_index: int = -1
        (* this attribute does not have any particular meaning, but it can be
          used by algorithms to label variables somehow, e.g., see ssa.ml *)
        val mutable m_mark: int = 0

        (* use it to compare variables, as the content may vary *)
        method id = var_id

        method get_sym_type = SymVar
        
        method as_var = (self :> var)

        method is_symbolic = self#has_flag HSymbolic
        method set_symbolic = self#add_flag HSymbolic

        method is_instrumental = self#has_flag HInstrumental
        method set_instrumental = self#add_flag HInstrumental

        method proc_name = m_proc_name
        method set_proc_name r = m_proc_name <- r

        method proc_index = m_proc_index
        method set_proc_index i = m_proc_index <- i

        method mark = m_mark
        method set_mark m = m_mark <- m

        (* get a qualified name with
           the prepending proctype and the index (if known) *)
        method qual_name =
            let q = if m_proc_name <> "" then m_proc_name else "" in
            let qi =
                if m_proc_index <> -1
                then sprintf "%s[%d]" q m_proc_index
                else q in
            if qi <> "" then qi ^ "." ^ name else name

        (* a qualified name as a mangled identifier, e.g.,
           when an external tool does not like dots and brackets *)
        method mangled_name =
            let q = if m_proc_name <> "" then m_proc_name else "" in
            let qi =
                if m_proc_index <> -1
                then sprintf "%s%dI" q m_proc_index
                else q in
            if qi <> "" then qi ^ "__" ^ name else name

        (* Make a copy of the variable, but keep id the same.
           It means that two copies will be considered similar
           (e.g., types and variable roles are the same). *)
        method copy new_name =
            let new_var = new var new_name self#id in
            new_var#set_flags self#get_flags;
            if self#is_symbolic then new_var#set_symbolic;
            if self#is_instrumental then new_var#set_instrumental;
            new_var#set_proc_name m_proc_name;
            new_var#set_proc_index m_proc_index;
            new_var#set_mark m_mark;
            new_var

        (* Make a copy of the variable and assign a fresh id. *)
        method fresh_copy new_name =
            let new_var = new var new_name (fresh_id ()) in
            new_var#set_flags self#get_flags;
            if self#is_symbolic then new_var#set_symbolic;
            if self#is_instrumental then new_var#set_instrumental;
            new_var#set_proc_name m_proc_name;
            new_var#set_proc_index m_proc_index;
            new_var#set_mark m_mark;
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


(* convenience functions *)
let new_var name = new var name (fresh_id ())    

let var_qname v = v#qual_name
let var_name v = v#get_name

module VarType =
    struct
        type t = var
        let compare (v1: var) (v2: var) = compare v1#id v2#id
    end

module VarSet = Set.Make(VarType)


exception Symbol_not_found of string

(* a symbol table *)
class symb_tab i_tab_name =
    object(self)
        val mutable tab: (string, symb) Hashtbl.t = Hashtbl.create 10
        val mutable parent: symb_tab option = None

        method tab_name = i_tab_name

        method add_symb name symb = Hashtbl.replace tab name symb

        method add_all_symb symb_list =
            List.iter (fun s -> Hashtbl.replace tab s#get_name s) symb_list

        method set_syms symb_list =
            tab <- Hashtbl.create (List.length symb_list);
            List.iter (fun s -> Hashtbl.replace tab s#get_name s) symb_list

        method lookup name =
            try Hashtbl.find tab name
            with Not_found ->
                match parent with
                | None -> (* XXX: show the position in the file! *)
                    let ts =
                        if i_tab_name <> "" 
                        then sprintf "(%s)" i_tab_name
                        else i_tab_name in
                    raise (Symbol_not_found
                        (sprintf "Variable %s is not declared %s" name ts))
                | Some p -> p#lookup name

        method find_or_error name = Hashtbl.find tab name

        method get_symb_pairs = Accums.hashtbl_as_list tab

        method get_symbs = Accums.hashtbl_vals tab

        method get_symb_pairs_rec: ((string * symb) list) =
            match parent with
            | Some p -> (Accums.hashtbl_as_list tab) @ p#get_symb_pairs_rec
            | None -> Accums.hashtbl_as_list tab

        method get_symbs_rec: symb list =
            match parent with
            | Some p -> (Accums.hashtbl_vals tab) @ p#get_symbs_rec
            | None -> Accums.hashtbl_vals tab

        method set_parent p = parent <- Some p
        method set_parent_opt p = parent <- p
        method get_parent = parent
    end


exception Type_not_found of string

class data_type i_basetype =
    object(self)
        (* the base type of a variable, e.g., int, byte, nat *)
        val m_basetype: var_type = i_basetype
        (* if this datatype represents not only one element, but an array *)
        val mutable m_isarray: bool = false
        (* the number of array elements, non-arrays have it set to 1 *)
        val mutable m_nelems: int = 1
        (* optional width specifier:
           showing how many bits this datatype requires *)
        val mutable m_nbits: int = 0
        (* optional range of (integer-like) values represented by this datatype:
           left margin is included, right margin is excluded *)
        val mutable m_range: int * int = (0, 0)

        method basetype = m_basetype
        method is_array = m_nelems > 1

        method nelems = m_nelems
        method set_nelems n = m_nelems <- n

        method nbits = m_nbits
        method set_nbits n = m_nbits <- n

        (* a range [l, r), the right bound is excluded *)
        method has_range = let l, r = m_range in r > l
        method range = m_range
        method range_len = let l, r = m_range in r - l
        method range_list =
           let l, r = m_range in Accums.range l r
        method set_range l r = m_range <- (l, r)
        method set_range_tuple (l, r) = m_range <- (l, r)

        method copy =
            let c = new data_type(m_basetype) in
            c#set_nelems m_nelems;
            c#set_nbits m_nbits;
            let l, r = m_range in
            c#set_range l r;
            c

        method to_s =
            let base_str = function
              | TBIT -> "bit"
              | TBYTE -> "byte"
              | TSHORT -> "short"
              | TINT -> "int"
              | TUNSIGNED -> "unsigned"
              | TCHAN -> "chan"
              | TMTYPE -> "mtype"
              | TPROPOSITION -> "proposition"
              | TUNDEF -> raise (Failure "Undefined type")
            in
            let l, r = m_range in
            let base = if not self#is_array && self#has_range && l >= 0
            then "unsigned" (* bitwidth will be specified *)
            else base_str m_basetype in
            sprintf "%s%s%s" base
                (if m_nbits > 0 then sprintf ":%d" m_nbits else "")
                (if self#is_array then sprintf "[%d]" m_nelems else "")
 
    end


let mk_int_range l r =
    let t = new data_type SpinTypes.TINT in
    t#set_range l r;
    t


(* This table binds integer identifiers of (variables) to the datatypes *)
class data_type_tab =
    object(self)
        val mutable m_tab: (int, data_type) Hashtbl.t = Hashtbl.create 5

        method has_type (v: var) = Hashtbl.mem m_tab v#id
        method get_type (v: var) =
            try Hashtbl.find m_tab v#id
            with Not_found ->
                self#print;
                raise (Type_not_found (sprintf "Type of %s (id=%d) not found"
                    v#get_name v#id))

        method set_type (v: var) (dtp: data_type) =
            Hashtbl.replace m_tab v#id dtp

        method set_all_types hash_tbl = m_tab <- hash_tbl

        method length = Hashtbl.length m_tab

        method copy =
            let new_t = new data_type_tab in
            new_t#set_all_types (Hashtbl.copy m_tab);
            new_t

        method print =
            let p (id, t) =
                printf "  %6d -> %s\n" id t#to_s
            in
            List.iter p (Accums.hashtbl_as_list m_tab)
    end


type 't expr =
    | Nop of string (* a comment *)
    | IntConst of int
    | Var of var
    | UnEx of 't * 't expr
    | BinEx of 't * 't expr * 't expr
    | Phi of var * var list (* a phi function for SSA purposes *)
    | LabelRef of string * string (* a reference to a process label *)


let is_nop = function
    | Nop _ -> true
    | _ -> false


let not_nop e = not (is_nop e) (* a shorthand *)

let is_c_true = function
    | IntConst i -> i > 0
    | _ -> false

let is_c_false = function
    | IntConst i -> i = 0
    | _ -> false

let is_var = function
    | Var _ -> true
    | _ -> false

let cmp_vars vx vy =
    String.compare vx#get_name vy#get_name

(* Sort the variables such that an unqualified name goes before a qualified
   one. Variables inside of their categories are sorted normally
 *)
let cmp_qual_vars vx vy =
    match (vx#qual_name == vx#get_name), (vy#qual_name == vy#get_name) with
    | true, true -> String.compare vx#get_name vy#get_name
    | false, false -> String.compare vx#qual_name vy#qual_name
    | false, true -> 1
    | true, false -> -1


let expr_used_vars (expression: 't expr) : var list =
    let rec find_used e =
        match e with
        | Var v -> if v#is_symbolic then [] else [v]
        | UnEx (_, f) -> find_used f
        | BinEx (_, f, g) -> List.append (find_used f) (find_used g)
        | _ -> []
    in
    Accums.list_sort_uniq cmp_vars (find_used expression)


let expr_list_used_vars (exprs: 't expr list) : var list =
    (* by using hashtbl we avoid duplicate elements *)
    let tbl = Hashtbl.create 10 in
    let collect_for_expr e =
        let vs = expr_used_vars e in
        List.iter (fun v -> Hashtbl.replace tbl v#qual_name v) vs
    in
    List.iter collect_for_expr exprs;
    List.sort cmp_vars (Accums.hashtbl_vals tbl)


let rec expr_exists func e =
    if (func e)
    then true
    else match e with
    | UnEx (_, f) -> expr_exists func f
    | BinEx (_, f, g) -> (expr_exists func f) || (expr_exists func g)
    | _ -> false


let not_symbolic = function
    | Var v -> not v#is_symbolic
    | _ -> false


let is_symbolic = function
    | Var v -> v#is_symbolic
    | _ -> false


let rec expr_forall func e = not (expr_exists (fun f -> not (func f)) e) 

(*
 A low-level statement, no block structure preserved (though gotos jump to
 valid labels corresponding to the blocks).
 The first field is always the identifier of a statement.
 *)
type 't stmt =
      Skip of int
    | Expr of int * 't expr
    | Decl of int * var * 't expr
    | Label of int * int
    | Atomic_beg of int | Atomic_end of int
    | D_step_beg of int | D_step_end of int
    | Goto of int * int
    | If of int * int list (* condition labels *)
    | Assert of int * 't expr
    | Assume of int * 't expr
    | Havoc of int * var (* forget about the current value of the variable *)
    | Print of int * string * 't expr list


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
    | If (id, _) -> id
    | Assert (id, _) -> id
    | Assume (id, _) -> id
    | Havoc (id, _) -> id
    | Print (id, _, _) -> id


let is_expr = function
    | Expr (_, _) -> true
    | _ -> false


let expr_of_stmt = function
    | Expr (_, e) -> e
    | _ -> raise (Failure "Expected Expr (_, e), found another statement")


let cmp_stmt s1 s2 =
    compare (stmt_id s1) (stmt_id s2)



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
    | If (_, opt_labs) -> If (new_id, opt_labs)
    | Assert (_, e) -> Assert (new_id, e)
    | Assume (_, e) -> Assume (new_id, e)
    | Havoc (_, v) -> Havoc (new_id, v)
    | Print (_, f, a) -> Print (new_id, f, a)


(* A middle-level statement, the block structure is still in place.
   Each statement has an identifier attached.
 *)
type 't mir_stmt =
    | MSkip of int
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
    | MUnsafe of int * string (* a statement never interpreted but copied*)
    | MDeclProp of int * var * 't atomic_expr
and 't atomic_expr =
    | PropAll of 't expr
    | PropSome of 't expr
    | PropGlob of 't expr (* refers to global variables only *)
    | PropAnd of 't atomic_expr * 't atomic_expr
    | PropOr of 't atomic_expr * 't atomic_expr
and 't mir_option =
    | MOptGuarded of 't mir_stmt list
    | MOptElse of 't mir_stmt list


let m_stmt_id = function
    | MSkip id -> id
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


let mk_comment text =
    MExpr (fresh_id (), Nop text)


let fresh_m_stmt = function
    | MSkip _ -> MSkip (fresh_id ())
    | MExpr (_, e) -> MExpr (fresh_id (), e)
    | MDecl (_, d, e) -> MDecl (fresh_id (), d, e)
    | MLabel (_, l) -> MLabel (fresh_id (), l)
    | MAtomic (_, s) -> MAtomic (fresh_id (), s)
    | MD_step (_, s) -> MD_step (fresh_id (), s)
    | MGoto (_, l) -> MGoto (fresh_id (), l)
    | MIf (_, s) -> MIf (fresh_id (), s)
    | MAssert (_, s) -> MAssert (fresh_id (), s)
    | MAssume (_, e) -> MAssume (fresh_id (), e)
    | MPrint (_, f, es) -> MPrint (fresh_id (), f, es)
    | MHavoc (_, e) -> MHavoc (fresh_id (), e)
    | MUnsafe (_, e) -> MUnsafe (fresh_id (), e)
    | MDeclProp (_, d, e) -> MDeclProp (fresh_id (), d, e)


let cmp_m_stmt s1 s2 =
    compare (m_stmt_id s1) (m_stmt_id s2)


let expr_of_m_stmt = function
    | MExpr (_, e) -> e
    | _ -> raise (Failure "Expected MExpr (_, e), found another statement")


let is_decl = function
    | Decl (_, _, _) -> true
    | _ -> false


let is_mdecl = function
    | MDecl (_, _, _) -> true
    | _ -> false


let stmt_list_used_vars (stmt_list: 't stmt list): var list =
    let to_expr lst = function
    | Expr (_, e) -> e :: lst
    | Assert (_, e) -> e :: lst
    | Assume (_, e) -> e :: lst
    | _ -> lst
    in
    expr_list_used_vars (List.fold_left to_expr [] stmt_list)


(* a process *)
class ['t] proc name_i active_expr_i =
    object(self)
        inherit symb name_i
        inherit symb_tab name_i as parent

        val mutable m_args: var list = []
        val mutable m_stmts: 't mir_stmt list = []
        (* a symbolic expression *)
        val mutable m_active_expr: 't expr = active_expr_i
        (* a provided clause if any *)
        val mutable m_provided_expr: 't expr = Nop ""

        method copy new_name =
            let new_p = new proc new_name m_active_expr in
            new_p#set_args m_args;
            new_p#set_stmts m_stmts;
            new_p#set_provided m_provided_expr;
            (new_p :> symb_tab)#add_all_symb self#get_symbs;
            new_p

        method set_args a = m_args <- a
        method get_args = m_args

        method set_stmts stmts =
            m_stmts <- stmts;
            let to_symb v = (v :> symb) in
            let not_var s = (s#get_sym_type <> SymVar) in
            let other_syms = List.filter not_var self#get_symbs in
            parent#set_syms ((List.map to_symb self#get_locals) @ other_syms)

        method get_stmts = m_stmts

        method set_active_expr e = m_active_expr <- e
        method get_active_expr = m_active_expr

        method set_provided e = m_provided_expr <- e
        method get_provided = m_provided_expr

        method labels_as_hash =
            let symbs = List.filter
                (fun (_, s) -> SymLab = s#get_sym_type)
                self#get_symb_pairs in
            let tbl = Hashtbl.create (List.length symbs) in
            let add_label (_, s) = Hashtbl.add tbl s#get_name s#as_label in
            List.iter add_label symbs;
            tbl

        method get_locals =
            let add_decl l = function
                | MDecl (_, v, _) -> v :: l
                | _ -> l
            in
            List.fold_left add_decl [] m_stmts
    end


let proc_replace_body (p: 't proc) (new_body: 't mir_stmt list) =
    let new_p = new proc p#get_name p#get_active_expr in
    new_p#set_args p#get_args;
    new_p#set_stmts new_body;
    (new_p :> symb_tab)#add_all_symb p#get_symbs;
    new_p


let map_vars map_fun ex =
    let mapv v =
        match map_fun v with
        | Var v -> v
        | _ -> raise (Failure "expected var")
    in
    let rec sub = function
    | Var v -> map_fun v
    | UnEx (t, l) -> UnEx (t, sub l)
    | BinEx (t, l, r) -> BinEx (t, sub l, sub r)
    | Phi (v, es) -> Phi (mapv v, List.map mapv es)
    | _ as e -> e
    in
    sub ex


type 't prog_unit = Proc of 't proc | Stmt of 't mir_stmt
    | Ltl of string * 't expr | EmptyUnit


let proc_of_unit = function
    | Proc p -> p
    | _ -> raise (Failure "Expected Proc p, found other unit")


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


(* miscellaneous statement traversing and substitution functions *)
let sub_basic_stmt
        (trav_fun: 'a mir_stmt -> 'a mir_stmt) (m_stmt: 'a mir_stmt)
        : 'a mir_stmt =
    let rec trav = function
    | MIf (id, opts) ->
        MIf (id, (List.map trav_opt opts))
    | MAtomic (id, body) ->
        MAtomic (id, List.map trav body)
    | MD_step (id, body) ->
        MD_step (id, List.map trav body)
    | _ as s -> trav_fun s

    and trav_opt = function
    | MOptGuarded body ->
        MOptGuarded (List.map trav body)
    | MOptElse body ->
        MOptElse (List.map trav body)
    in
    trav m_stmt


let sub_basic_stmt_with_list
        (trav_fun: 'a mir_stmt -> 'a mir_stmt list) (stmts: 'a mir_stmt list)
        : 'a mir_stmt list =
    let rec fold lst s =
        lst @ (trav s)

    and trav = function
        | MIf (id, opts) ->
            [ MIf (id, List.map trav_opt opts) ]
        | MAtomic (id, body) ->
            [ MAtomic (id, List.fold_left fold [] body) ]
        | MD_step (id, body) ->
            [ MD_step (id, List.fold_left fold [] body) ]
        | _ as s -> trav_fun s

    and trav_opt = function
        | MOptGuarded body ->
            MOptGuarded (List.fold_left fold [] body)
        | MOptElse body ->
            MOptElse (List.fold_left fold [] body)
    in
    List.fold_left fold [] stmts


(* the general way to do substitutions *)
let sub_stmt_with_list
        (sub_fun: 't mir_stmt -> (bool * 't mir_stmt list))
        (seq: 't mir_stmt list): 't mir_stmt list =
    let rec sub rs s =
        let no_deeper, nss = sub_fun s in
        if no_deeper      (* the user did the substitution as they like *)
        then nss @ rs
        else match s with (* go deeper *)
            | MIf (id, opts) ->
                (MIf (id, List.map sub_opt opts)) :: rs

            | MAtomic (id, body) ->
                (MAtomic (id, List.fold_left sub [] (List.rev body))) :: rs

            | MD_step (id, body) ->
                (MD_step (id, List.fold_left sub [] (List.rev body))) :: rs

            | _ as s -> s :: rs

    and sub_opt = function
    | MOptGuarded body ->
        MOptGuarded (List.fold_left sub [] (List.rev body))

    | MOptElse body ->
        MOptElse (List.fold_left sub [] (List.rev body))
    in
    List.fold_left sub [] (List.rev seq)


let map_expr_in_stmt (map_expr: 'a expr -> 'a expr) (stmt: 'a mir_stmt)
        : 'a mir_stmt =
    let rec map_atomic = function
    | PropAll e -> PropAll (map_expr e)
    | PropSome e -> PropSome (map_expr e)
    | PropGlob e -> PropGlob (map_expr e)
    | PropAnd (l, r) -> PropAnd (map_atomic l, map_atomic r)
    | PropOr (l, r) -> PropOr (map_atomic l, map_atomic r)
    in
    let rec trav = function
    | MIf (id, opts) ->
        MIf (id, (List.map trav_opt opts))
    | MAtomic (id, body) ->
        MAtomic (id, List.map trav body)
    | MD_step (id, body) ->
        MD_step (id, List.map trav body)

    | MExpr (id, e) ->
        MExpr (id, map_expr e)
    | MDecl (id, v, e) ->
        MDecl (id, v, map_expr e)
    | MAssert (id, e) ->
        MAssert (id, map_expr e)
    | MAssume (id, e) ->
        MAssume (id, map_expr e)
    | MPrint (id, str, es) ->
        MPrint (id, str, List.map map_expr es)
    | MDeclProp (id, v, ae) ->
        MDeclProp (id, v, map_atomic ae)
    | _ as s -> s

    and trav_opt = function
    | MOptGuarded body ->
        MOptGuarded (List.map trav body)
    | MOptElse body ->
        MOptElse (List.map trav body)
    in
    trav stmt


let map_expr_in_lir_stmt (map_expr: 'a expr -> 'a expr) (stmt: 'a stmt)
        : 'a stmt =
    let sub_var v =
        match map_expr (Var v) with
        | Var nv -> nv
        | _ -> raise (Failure "expected var, found something else")
    in
    match stmt with
    | Expr (id, e) -> Expr (id, map_expr e)
    | Decl (id, v, e) -> Decl (id, sub_var v, map_expr e)
    | Assert (id, e) -> Assert (id, map_expr e)
    | Assume (id, e) -> Assume (id, map_expr e)
    | Havoc (id, v) -> Havoc (id, sub_var v)
    | Print (id, fmt, es) -> Print (id, fmt, List.map map_expr es)
    | _ as e -> e

