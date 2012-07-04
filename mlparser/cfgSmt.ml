(* Encoding a CFG as an SMT formula, assuming that CFG is in SSA. *)

open Printf;;

open Accums;;
open Spin;;
open Spin_ir;;
open Spin_ir_imp;;
open Cfg;;
open Ssa;;
open Smt;;

(* convert a list of expressions [e1, ..., ek] to a binary tree
   (tok, e1, (tok, e2, (... (tok, e(k-1), ek) ...))).
   Nop expressions are ignored.
 *)
let list_to_binex tok lst =
    let join_e ae e =
        if e <> Nop
        then if ae <> Nop then BinEx (tok, ae, e) else e
        else ae
    in
    List.fold_left join_e Nop lst
;;

(*
 XXX: this translation does not work with a control flow graph like this:
     A -> (B, C); B -> D; C -> D; B -> C.
 To handle this case two copies of C must be introduced.
 *)
let block_to_constraints (bb: 't basic_block) =
    let at_var i = Var (new var (sprintf "at_%d" i)) in
    (* control flow passes to a successor: at_i -> (at_s1 || ... || at_sk) *)
    let succ_labs = bb#succ_labs in
    let flow_succ = List.fold_left
        (fun e successor -> BinEx (OR, e, (at_var successor#label)))
        (UnEx (NEG, (at_var bb#label))) bb#get_succ in
    let n_succ = List.length bb#get_succ in
    (* at most one successor takes the control *)
    let mk_mux (pair: int list) =
        let i, j = (List.hd pair), (List.nth pair 1) in
        let cond = BinEx (OR,
            UnEx (NEG, at_var (List.nth succ_labs i)),
            UnEx (NEG, at_var (List.nth succ_labs j))) in
        if i < j then cond else Nop
    in
    let loc_mux =
        list_to_binex (AND) (List.map mk_mux (mk_product (range 0 n_succ) 2)) in
    (* convert statements *)
    let convert tl = function
        | Expr (id, Phi (lhs, rhs)) ->
            (* (at_i -> x = x_i) for x = phi(x_1, ..., x_k) *)
            let pred_labs = bb#pred_labs in
            let n_preds = List.length pred_labs in
            let pred_selects_arg i =
                BinEx (OR,
                    UnEx (NEG, at_var (List.nth pred_labs i)),
                    BinEx (EQ, Var lhs, Var (List.nth rhs i)))
            in
            let exprs = (List.map pred_selects_arg (range 0 n_preds)) in
            SmtExpr (list_to_binex AND exprs) :: tl

        | Expr (_, BinEx (ASGN, lhs, rhs)) ->
            SmtExpr (BinEx (EQ, lhs, rhs)) :: tl

        | Expr (_, Nop) ->
            tl (* skip this *)
        | Expr (id, e) ->
            (* at_i -> e *)
            SmtExpr (BinEx (OR, UnEx (NEG, at_var bb#label), e)) :: tl

        | Decl (_, v, e) -> SmtDecl (v, e) :: tl
        | Assume (_, e) -> (SmtExpr e) :: tl
        | Assert (_, e) -> (SmtExpr e) :: tl
        | Skip _ -> tl
        | _ -> tl (* ignore all control flow constructs *)
    in
    let smt_es = (List.rev (List.fold_left convert [] bb#get_seq)) in
    let smt_es = if flow_succ <> Nop
        then SmtExpr flow_succ :: smt_es
        else smt_es in
    if loc_mux <> Nop then SmtExpr loc_mux :: smt_es else smt_es
;;

let is_smt_decl = function
    | SmtDecl _ -> true
    | _ -> false
;;

let cfg_to_constraints cfg =
    (* introduce variables at_i *)
    (* TODO: declare them somewhere! *)
    let cons = List.concat (List.map block_to_constraints cfg#block_list) in
    let decls, non_decls = List.partition is_smt_decl cons in
    let cons = decls @ non_decls in
    printf "SMT constraints: \n";
    List.iter (fun s -> printf "%s\n" (smt_expr_s s)) cons;
    cons
;;
