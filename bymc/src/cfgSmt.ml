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

(*
 XXX: this translation does not work with a control flow graph like this:
     A -> (B, C); B -> D; C -> D; B -> C.
 To handle this case two copies of C must be introduced.
 *)
let block_to_constraints (proc: 't proc)
        (new_sym_tab: symb_tab)
        (new_type_tab: data_type_tab)
        (bb: 't basic_block): (Spin.token mir_stmt list) =
    (*printf "block_to_constraints %s: %d\n" proc#get_name bb#label; flush stdout; *)
    let succ_var bb =
        let name = sprintf "succ%d" bb#label in
        try Var ((new_sym_tab#lookup name)#as_var)
        with Symbol_not_found _ ->
            let nv = new_var name in 
            nv#set_proc_name proc#get_name;
            let tp = new data_type SpinTypes.TINT in
            (* value 0 means 'disabled', the exit block should be enabled *)
            let r = max 2 (1 + List.length bb#get_succ) in
            tp#set_range 0 r;
            new_type_tab#set_type nv tp;
            new_sym_tab#add_symb nv#get_name (nv :> symb);
            Var nv
    in
    (* control flow passes to a successor: at_i -> (at_s1 || ... || at_sk) *)
    let n_succ = List.length bb#get_succ in
    let flow_succ =
        let some_pred_enables =
            let for_pred p =
                let pos = 1 + (list_find_pos bb p#get_succ) in
                BinEx (EQ, succ_var p, Const pos)
            in
            if bb#get_pred <> []
            then BinEx (EQUIV,
                         BinEx (NE, succ_var bb, Const 0),
                         list_to_binex OR (List.map for_pred bb#get_pred))
            else Nop ""
        in
        let for_succ s si =
            BinEx (IMPLIES, BinEx (EQ, succ_var bb, Const si),
                          BinEx (NE, succ_var s, Const 0))
        in
        if n_succ <> 0
        then mkez some_pred_enables
            (*
            mkez (list_to_binex AND
            ((List.map2 for_succ bb#get_succ (range 1 (1 + n_succ)))
            @ some_pred_enables))
            *)
        else mkez (Nop "")
    in
    (* convert statements *)
    let n_pred = List.length bb#get_pred in
    let at_impl_expr e =
        (*
        let is_succ p =
            let pos = 1 + (list_find_pos bb p#get_succ) in
            BinEx (NE, succ_var p, Const pos) in
        let inactive = list_to_binex AND (List.map is_succ bb#get_pred) in
        *)
        BinEx (IMPLIES, BinEx (NE, succ_var bb, Const 0), e)
    in
    let convert (tl: Spin.token mir_stmt list) (s: Spin.token stmt):
            Spin.token mir_stmt list=
        match s with
        | Expr (id, (Phi (lhs, rhs) as e)) ->
            (* (at_i -> x = x_i) for x = phi(x_1, ..., x_k) *)
            let pred_labs = bb#pred_labs in
            let n_preds = List.length pred_labs in
            let pred_selects_arg p i =
                BinEx (OR,
                    BinEx (EQ, succ_var p, Const 0),
                    BinEx (EQ, Var lhs, Var (List.nth rhs i)))
            in
            let exprs = List.map2 pred_selects_arg bb#get_pred (range 0 n_preds)
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


let cfg_to_constraints proc new_sym_tab new_type_tab cfg =
    let cons_lists =
        List.map (block_to_constraints proc new_sym_tab new_type_tab)
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
            nv#set_proc_name proc#get_name;
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
        printf "SMT constraints: \n";
        let print_stmt = function
        | MExpr (_, e) -> printf "%s\n" (expr_to_smt e)
        | _ -> () in
        List.iter print_stmt cons;
    end;
    (mkez activation) :: cons

