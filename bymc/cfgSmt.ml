(* Encoding a CFG as an SMT formula, assuming that CFG is in SSA. *)

open Printf;;

open Accums;;
open Spin;;
open SpinIr;;
open SpinIrImp;;
open Cfg;;
open Ssa;;
open Smt;;
open Debug;;

class ['t] proc_xducer (i_orig_proc: 't proc) (i_cons: 't expr list) =
    object
        val orig_proc = i_orig_proc
        val transition_cons: 't expr list = i_cons

        method get_orig_proc = orig_proc
        method get_trans_form = transition_cons
    end
;;

(*
 XXX: this translation does not work with a control flow graph like this:
     A -> (B, C); B -> D; C -> D; B -> C.
 To handle this case two copies of C must be introduced.
 *)
let block_to_constraints (bb: 't basic_block) =
    let at_var i =
        let nv = new var (sprintf "at_%d" i) in 
        nv#set_type SpinTypes.TBIT;
        Var nv
    in
    (* the entry block always gains control! *)
    let entry_starts = if bb#label <> 0 then Nop "" else at_var 0 in
    (* control flow passes to a successor: at_i -> (at_s1 || ... || at_sk) *)
    let succ_labs = bb#succ_labs in
    let n_succ = List.length bb#get_succ in
    let flow_succ =
        if n_succ <> 0
        then List.fold_left
            (fun e successor -> BinEx (OR, e, (at_var successor#label)))
            (UnEx (NEG, (at_var bb#label))) bb#get_succ
        else Nop ""
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
        list_to_binex (AND) (List.map mk_mux (mk_product (range 0 n_succ) 2)) in
    (* convert statements *)
    let at_impl_expr e =
        BinEx (OR, UnEx (NEG, at_var bb#label), e) in
    let convert s tl =
        match s with
        | Expr (_, Phi (lhs, rhs)) ->
            (* (at_i -> x = x_i) for x = phi(x_1, ..., x_k) *)
            let pred_labs = bb#pred_labs in
            let n_preds = List.length pred_labs in
            let pred_selects_arg i =
                BinEx (OR,
                    UnEx (NEG, at_var (List.nth pred_labs i)),
                    BinEx (EQ, Var lhs, Var (List.nth rhs i)))
            in
            let exprs = (List.map pred_selects_arg (range 0 n_preds)) in
            (list_to_binex AND exprs) :: tl

        (* crazy array update form imposed by SSA *)
        | Expr (_, BinEx (ASGN, Var new_arr,
                    BinEx (ARR_UPDATE,
                           BinEx (ARR_ACCESS, Var old_arr, idx), rhs))) ->
            let mk_arr v i = BinEx (ARR_ACCESS, Var v, i) in
            let keep_val l i =
                let eq = BinEx (EQ,
                    mk_arr new_arr (Const i), mk_arr old_arr (Const i)) in
                at_impl_expr (BinEx (OR, BinEx (EQ, idx, Const i), eq)) :: l in
            (at_impl_expr (BinEx (EQ, mk_arr new_arr idx, rhs)))
            ::
            List.fold_left keep_val tl (range 0 new_arr#get_num_elems)

        | Expr (_, BinEx (ASGN, lhs, rhs)) ->
            (at_impl_expr (BinEx (EQ, lhs, rhs))) :: tl

        | Expr (_, Nop _) ->
            tl (* skip this *)
        | Expr (_, e) ->
            (* at_i -> e *)
            (at_impl_expr e) :: tl

        | Decl (_, v, e) -> (at_impl_expr (BinEx (EQ, Var v, e))) :: tl
        | Assume (_, e) -> (at_impl_expr e) :: tl
        | Assert (_, e) -> (at_impl_expr e) :: tl
        | Skip _ -> tl
        | _ -> tl (* ignore all control flow constructs *)
    in
    let smt_es = (List.fold_right convert bb#get_seq []) in
    let n_cons e es = if not_nop e then e :: es else es in
    n_cons entry_starts (n_cons flow_succ (n_cons loc_mux smt_es))
;;

let cfg_to_constraints cfg =
    let cons = List.concat (List.map block_to_constraints cfg#block_list) in
    if may_log DEBUG
    then begin
        printf "SMT constraints: \n";
        List.iter (fun s -> printf "%s\n" (expr_to_smt s)) cons;
    end;
    cons
;;
