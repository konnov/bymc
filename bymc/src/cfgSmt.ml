(* Encoding a CFG as an SMT formula, assuming that CFG is in SSA. *)

open Printf

open Accums
open Spin
open SpinIr
open SpinIrImp
open Cfg
open Ssa
open Smt
open Debug

let mke id e = MExpr (id, e) 
let mkez e = MExpr (fresh_id (), e)

let get_entry_loc proc =
    (proc#lookup "at0")#as_var


(* Find all blocks that have exactly one successor (we call them options).
   Map these blocks to their successors transitively. As these blocks do not
   have to choose their successor, they do not need the succ variable, and
   their activation is defined via their parents.
 *)
let find_choices cfg =
    let tab = Hashtbl.create (List.length cfg#block_list) in
    let rec find_edge b l p =
        if (List.length p#get_succ) > 1
        then
            (* this node has a choice, return the edge *)
            let pos = list_find_pos b p#get_succ in
            (p, pos) :: l
        else
            List.fold_left (find_edge p) l p#get_pred
    in
    let each_block b =
        let edges = List.map (find_edge b []) b#get_pred in
        Hashtbl.replace tab b#label edges
    in
    List.iter each_block cfg#block_list;
    tab


(*
 XXX: this translation does not work with a control flow graph like this:
     A -> (B, C); B -> D; C -> D; B -> C.
 To handle this case two copies of C must be introduced.
 *)
let block_to_constraints (proc_name: string)
        (new_sym_tab: symb_tab)
        (new_type_tab: data_type_tab)
        (choices: (int, ('t basic_block * int) list list) Hashtbl.t)
        (bb: 't basic_block): (Spin.token mir_stmt list) =
    (*printf "block_to_constraints %s: %d\n" proc#get_name bb#label; flush stdout; *)
    let succ_var bb =
        let name = sprintf "succ%d" bb#label in
        try Var ((new_sym_tab#lookup name)#as_var)
        with Symbol_not_found _ ->
            let nv = new_var name in 
            nv#set_proc_name proc_name;
            let tp = new data_type SpinTypes.TINT in
            (* value 0 means 'disabled', the exit block should be enabled *)
            let r = max 2 (1 + List.length bb#get_succ) in
            tp#set_range 0 r;
            new_type_tab#set_type nv tp;
            new_sym_tab#add_symb nv#get_name (nv :> symb);
            Var nv
    in
    if bb#label = 0 (* immediately introduce succ0 *)
    then ignore (succ_var bb);

    (* control flow passes to a successor: at_i -> (at_s1 || ... || at_sk) *)
    let parents_cons l edges =
        let f l (p, i) = BinEx (EQ, succ_var p, Const (1 + i)) :: l in
        List.fold_left f l edges
    in
    let parents_activate =
        let flat =
            List.fold_left parents_cons [] (Hashtbl.find choices bb#label) in 
        list_to_binex OR flat
    in
    let n_succ = List.length bb#get_succ in
    let n_pred = List.length bb#get_pred in
    let flow_succ =
        if n_succ > 1 && n_pred <> 0
        then if is_nop parents_activate
            then mkez (BinEx (NE, succ_var bb, Const 0))
            else mkez (* predecessors activate *)
                (BinEx (EQUIV, BinEx (NE, succ_var bb, Const 0), parents_activate))
        else mkez (Nop "") (* no succ variable for this block *)
    in
    (* convert statements *)
    let at_impl_expr e =
        if n_succ > 1
        (* we have the variable succ${i} for this block *)
        then BinEx (IMPLIES, BinEx (NE, succ_var bb, Const 0), e)
        else (* use the parents' variables *)
            BinEx (IMPLIES, parents_activate, e)
    in
    let convert (tl: Spin.token mir_stmt list) (s: Spin.token stmt):
            Spin.token mir_stmt list=
        match s with
        | Expr (id, (Phi (lhs, rhs) as e)) ->
            (* (at_i -> x = x_i) for x = phi(x_1, ..., x_k) *)
            let choices = Hashtbl.find choices bb#label in
            let n_preds = List.length bb#get_pred in
            let pred_selects_arg cs i =
                BinEx (IMPLIES,
                    list_to_binex OR (parents_cons [] cs),
                    BinEx (EQ, Var lhs, Var (List.nth rhs i)))
            in
            let exprs = List.map2 pred_selects_arg choices (range 0 n_preds)
            in
            (* keep ids and keep comments to ease debugging *)
            (mke id (Nop (sprintf "%d: %s" id (expr_s e))))
                :: (mkez (list_to_binex AND exprs)) :: tl

        (* crazy array update form imposed by SSA *)
        | Expr (id, (BinEx (ASGN, Var new_arr,
                BinEx (ARR_UPDATE,
                    BinEx (ARR_ACCESS, Var old_arr, idx), rhs)) as e)) ->
            let mk_arr v i = BinEx (ARR_ACCESS, Var v, i) in
            let keep_val l i =
                let eq = BinEx (EQ,
                    mk_arr new_arr (Const i), mk_arr old_arr (Const i)) in
                (mkez (at_impl_expr (BinEx (OR, BinEx (EQ, idx, Const i), eq))))
                :: l
            in
            let nelems = (new_type_tab#get_type new_arr)#nelems in
                (mke id (Nop (sprintf "%d: %s" id (expr_s e))))
                :: (mkez (at_impl_expr (BinEx (EQ, mk_arr new_arr idx, rhs))))
                :: (List.fold_left keep_val tl (range 0 nelems))

        | Expr (id, (BinEx (ASGN, lhs, rhs) as e)) ->
            (mke id (Nop (expr_s e)))
                :: (mkez (at_impl_expr (BinEx (EQ, lhs, rhs)))) :: tl

        | Expr (_, Nop _) ->
            tl (* skip this *)

        | Expr (id, e) ->
            (* at_i -> e *)
            (mke id (Nop (expr_s e))) :: (mkez (at_impl_expr e)) :: tl

        | Decl (id, v, e) ->
            (mke id (Nop (sprintf "%s = %s" v#get_name (expr_s e))))
            :: (mkez (at_impl_expr (BinEx (EQ, Var v, e)))) :: tl

        | Assume (id, e) ->
            (mke id (Nop (sprintf "assume(%s)" (expr_s e))))
            :: (mkez (at_impl_expr e)) :: tl

        | Assert (id, e) ->
            (mke id (Nop (sprintf "assert(%s)" (expr_s e))))
            :: (mkez (at_impl_expr e)) :: tl

        | Skip _ -> tl
        | _ -> tl (* ignore all control flow constructs *)
    in
    let smt_es = (List.fold_left convert [] (List.rev bb#get_seq)) in
    let stmt_not_nop = function
        | MExpr (_, Nop _) -> false
        | _ -> true
    in
    let n_cons e es = if stmt_not_nop e then e :: es else es in
    (* old implementation: the entry block always gains control *)
    (*
    let entry_starts =
        if bb#label <> 0 then mkez (Nop "") else mkez (at_var 0) in
    n_cons entry_starts (n_cons flow_succ (n_cons loc_mux smt_es))
    *)
    (* new implementation: when there are several processes,
       a higher level function must pick a process to move *)
    n_cons flow_succ smt_es


(* Translate block constraints without flow constraints between blocks
   (intrablock constraints if you like).
   It is useful when dealing with one path (see bddPass).
 *)
let block_intra_cons (proc_name: string)
        (type_tab: data_type_tab) (new_type_tab: data_type_tab)
        (bb: 't basic_block): (Spin.token mir_stmt list) =
    let convert (tl: Spin.token mir_stmt list) (s: Spin.token stmt):
            Spin.token mir_stmt list=
        match s with
        | Expr (_, (Phi (_, _))) ->
            raise (CfgError "Unexpected phi func (use move_phi_to_blocks)")

        | Expr (_, (BinEx (ASGN, _,
            BinEx (ARR_UPDATE,
                BinEx (ARR_ACCESS, _, _), _)))) ->
            raise (CfgError ("Unexpected array update: " ^ (stmt_s s)))

        | Expr (id, (BinEx (ASGN, lhs, rhs) as e)) ->
            (mke id (Nop (expr_s e)))
                :: (mkez (BinEx (EQ, lhs, rhs))) :: tl

        | Expr (_, Nop _) ->
            tl (* skip this *)
        | Expr (id, e) ->
            (* at_i -> e *)
            (mke id (Nop (expr_s e))) :: (mkez e) :: tl

        | Decl (id, v, e) ->
            (mke id (Nop (sprintf "%s = %s" v#get_name (expr_s e))))
            :: (mkez (BinEx (EQ, Var v, e))) :: tl
        | Assume (id, e) ->
            (mke id (Nop (sprintf "assume(%s)" (expr_s e))))
            :: (mkez e) :: tl
        | Assert (id, e) ->
            (mke id (Nop (sprintf "assert(%s)" (expr_s e))))
            :: (mkez e) :: tl
        | Skip _ -> tl
        | _ -> tl (* ignore all control flow constructs *)
    in
    List.fold_left convert [] (List.rev bb#get_seq)


let cfg_to_constraints proc_name new_sym_tab new_type_tab cfg =
    let choices = find_choices cfg in
    let cons_lists =
        List.map (block_to_constraints proc_name new_sym_tab new_type_tab choices)
            cfg#block_list
    in
    let cons = List.concat cons_lists in
    (* Create a variable that encoding the number of an incoming predecessor
       block. If the block is not activated during execution, then this
       variables is set to zero.                                        *)
    let at_var =
        let name = "at0" in
        try Var ((new_sym_tab#lookup name)#as_var)
        with Symbol_not_found _ ->
            let nv = new_var name in 
            nv#set_proc_name proc_name;
            let tp = new data_type SpinTypes.TBIT in
            new_type_tab#set_type nv tp;
            new_sym_tab#add_symb nv#get_name (nv :> symb);
            Var nv
    in
    let activation =
        let succ0 = Var (new_sym_tab#lookup "succ0")#as_var in
        BinEx (EQUIV, at_var, BinEx (NE, succ0, Const 0))
    in
    if may_log DEBUG
    then begin
        printf "constraints: \n";
        let print_stmt = function
        | MExpr (_, e) -> printf "%s\n" (expr_s e)
        | _ -> () in
        List.iter print_stmt cons;
    end;
    (mkez activation) :: cons

