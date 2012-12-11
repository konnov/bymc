(*
  This pass transforms a transducer into a boolean representation,
  to be used in a BDD model checker.

  Igor Konnov, 2012
 *)

open Printf

open Spin
open SpinIr
open SpinIrImp

exception Bdd_error of string

let proc_to_bdd prog proc =
    let rec bits_of_expr pos = function
        | Var v ->
            if (Program.get_type prog v)#basetype != SpinTypes.TBIT
            then raise (Bdd_error
                (sprintf "Variables %s must be boolean" v#get_name))
            else if pos
            then Bits.V v#get_name
            else Bits.NV v#get_name
        | BinEx (ASGN, Var v, Const i) ->
            if pos
            then Bits.VeqI (v#get_name, i)
            else Bits.VneI (v#get_name, i)
        | BinEx (EQ, Var v, Const i) ->
            if pos
            then Bits.VeqI (v#get_name, i)
            else Bits.VneI (v#get_name, i)
        | BinEx (NE, Var v, Const i) ->
            if pos
            then Bits.VneI (v#get_name, i)
            else Bits.VeqI (v#get_name, i)
        | BinEx (EQ, Var x, Var y) ->
            if pos
            then Bits.EQ (x#get_name, y#get_name)
            else Bits.NE (x#get_name, y#get_name)
        | BinEx (NE, Var x, Var y) ->
            if pos
            then Bits.NE (x#get_name, y#get_name)
            else Bits.EQ (x#get_name, y#get_name)
        | BinEx (GT, Var x, Var y) ->
            if pos
            then Bits.GT (x#get_name, y#get_name)
            else Bits.LE (x#get_name, y#get_name)
        | BinEx (GE, Var x, Var y) ->
            if pos
            then Bits.GE (x#get_name, y#get_name)
            else Bits.LT (x#get_name, y#get_name)
        | BinEx (LT, Var x, Var y) ->
            if pos
            then Bits.LT (x#get_name, y#get_name)
            else Bits.GE (x#get_name, y#get_name)
        | BinEx (LE, Var x, Var y) ->
            if pos
            then Bits.LE (x#get_name, y#get_name)
            else Bits.GT (x#get_name, y#get_name)
        | BinEx (AND, l, r) ->
            Bits.AND [bits_of_expr pos l; bits_of_expr pos r]
        | BinEx (OR, l, r) ->
            Bits.OR [bits_of_expr pos l; bits_of_expr pos r]
        | UnEx (NEG, l) ->
            bits_of_expr (not pos) l
        | Nop text ->
            Bits.ANNOTATION ("{" ^ text ^ "}", Bits.B1)
        | _ as e ->
            Bits.ANNOTATION (expr_tree_s e, Bits.B1)
            (*
            raise (Bdd_error ("Cannot convert to BDD: " ^ (expr_s e)))
            *)
    in
    let to_bits = function
        | MExpr (_, e) ->
            bits_of_expr true e
        | _ as s -> 
            raise (Bdd_error ("Cannot convert to BDD: " ^ (mir_stmt_s s)))
    in
    let bits = Bits.AND (List.map to_bits proc#get_stmts) in
    let out = open_out (sprintf "%s.bdd" proc#get_name) in
    let ff = Format.formatter_of_out_channel out in
    Bits.format_bv_form ff bits;
    close_out out


let enum_in_outs solver prog proc =
    let exprs = List.map expr_of_m_stmt proc#get_stmts in
    let decls = expr_list_used_vars exprs in
    solver#push_ctx;
    solver#set_need_evidence true;
    List.iter solver#append_var_def decls;
    List.iter (fun e -> let _ = solver#append_expr e in ()) exprs;
    if solver#check then begin
        printf "One value to take...\n";
        let vals = Refinement.parse_smt_evidence prog solver in
        Refinement.pretty_print_exprs (Hashtbl.find vals 0);
        Refinement.pretty_print_exprs (Hashtbl.find vals 1);
    end;
    solver#pop_ctx


let transform_to_bdd solver caches prog =
    List.iter (proc_to_bdd prog) (Program.get_procs prog);
    (*
    List.iter (enum_in_outs solver prog) (Program.get_procs prog)
    *)

