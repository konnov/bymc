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

(*
 XXX: this translation does not work with a control flow graph like this:
     A -> (B, C); B -> D; C -> D; B -> C.
 To handle this case two copies of C must be introduced.
 *)
let block_to_constraints (new_type_tab: data_type_tab)
        (bb: 't basic_block): (Spin.token mir_stmt list) =
    let at_var i =
        let nv = new_var (sprintf "at_%d" i) in 
        new_type_tab#set_type nv (new data_type SpinTypes.TBIT);
        Var nv
    in
    let mke id e = MExpr (id, e) in
    let mkez e = MExpr (-1, e) in
    (* the entry block always gains control! *)
    let entry_starts =
        if bb#label <> 0 then mkez (Nop "") else mkez (at_var 0) in
    (* control flow passes to a successor: at_i -> (at_s1 || ... || at_sk) *)
    let succ_labs = bb#succ_labs in
    let n_succ = List.length bb#get_succ in
    let flow_succ =
        if n_succ <> 0
        then
            (mkez (List.fold_left
                (fun e successor ->
                    BinEx (OR, e, (at_var successor#label)))
                    (UnEx (NEG, (at_var bb#label))) bb#get_succ))
        else (mkez (Nop ""))
    in
    (* at most one successor takes the control *)
    let mk_mux (pair: int list) =
        let i, j = (List.hd pair), (List.nth pair 1) in
        let cond = BinEx (OR,
            UnEx (NEG, at_var (List.nth succ_labs i)),
            UnEx (NEG, at_var (List.nth succ_labs j))) in
        if i < j then cond else Nop ""
    in
    let loc_mux =
        (mkez (list_to_binex (AND)
                (List.map mk_mux (mk_product (range 0 n_succ) 2))))
    in
    (* convert statements *)
    let at_impl_expr e =
        BinEx (OR, UnEx (NEG, at_var bb#label), e) in
    let convert (s: Spin.token stmt) (tl: Spin.token mir_stmt list):
            Spin.token mir_stmt list=
        match s with
        | Expr (id, (Phi (lhs, rhs) as e)) ->
            (* (at_i -> x = x_i) for x = phi(x_1, ..., x_k) *)
            let pred_labs = bb#pred_labs in
            let n_preds = List.length pred_labs in
            let pred_selects_arg i =
                BinEx (OR,
                    UnEx (NEG, at_var (List.nth pred_labs i)),
                    BinEx (EQ, Var lhs, Var (List.nth rhs i)))
            in
            let exprs = (List.map pred_selects_arg (range 0 n_preds)) in
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
                (mkez (at_impl_expr (BinEx (OR, BinEx (EQ, idx, Const i), eq)))) :: l in
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
    let smt_es = (List.fold_right convert bb#get_seq []) in
    let stmt_not_nop = function
        | MExpr (_, Nop _) -> false
        | _ -> true
    in
    let n_cons e es = if stmt_not_nop e then e :: es else es in
    n_cons entry_starts (n_cons flow_succ (n_cons loc_mux smt_es))

let cfg_to_constraints new_type_tab cfg =
    let cons_lists =
        (List.map (block_to_constraints new_type_tab) cfg#block_list) in
    let cons = List.concat cons_lists in
    if may_log DEBUG
    then begin
        printf "SMT constraints: \n";
        let print_stmt = function
        | MExpr (_, e) -> printf "%s\n" (expr_to_smt e)
        | _ -> () in
        List.iter print_stmt cons;
    end;
    cons
