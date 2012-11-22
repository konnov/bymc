open Printf

open AbsBasics
open Spin
open SpinIr
open SpinIrImp
open Smt

open Accums
open Debug

exception Found of int;;

class pia_domain conds_i =
    object(self)
        val mutable conds = conds_i      (* thresholds *)
        (* symbolic intervals, i.e., triples of
            (abstract value, left cond, right cond) *)
        val mutable cond_intervals = []
        val mutable val_map = Hashtbl.create 10 (* from a cond to a value *)

        method print =
            log INFO " # Abstract domain:";
            let rmap = hashtbl_inverse val_map in
            let print_cond i =
                let c = Hashtbl.find rmap i in
                log INFO (sprintf "   d%d -> %s" i (expr_s c))
            in
            List.iter print_cond (range 0 (List.length conds))
        
        initializer
            List.iter
                (fun c -> Hashtbl.add val_map c (Hashtbl.length val_map))
                conds;
            let _, tuples =
                List.fold_left (fun (i, l) (a, b) -> (i + 1, (i, a, b) :: l))
                    (0, [])
                    (List.combine conds (List.append (List.tl conds) [Nop ""]))
            in
            cond_intervals <- tuples

        method length = List.length conds

        method map_concrete (solver: yices_smt) (symb_expr: 't expr) =
            try
                List.iter
                    (fun (_, l, r) ->
                        solver#push_ctx;
                        solver#append_assert
                            (expr_to_smt (BinEx (GE, symb_expr, l)));
                        if not_nop r
                        then solver#append_assert
                            (expr_to_smt (BinEx (LT, symb_expr, r)));
                        let sat = solver#check in
                        solver#pop_ctx;
                        if sat then raise (Found (Hashtbl.find val_map l));
                    ) cond_intervals;
                raise (Abstraction_error
                    (sprintf "No abstract value for %s" (expr_s symb_expr)))
            with Found i ->
                (Const i: Spin.token expr)

        method expr_is_concretization exp abs_val =
            (* given an abstract value abs_val, constrain exp to be a concretization
               of abs_val, i.e. create a boolean expression over exp *)
            let (_, l, r) = List.find (fun (a, _, _) -> a = abs_val) cond_intervals in
            let left = BinEx (GE, exp, l) in
            if not_nop r
            then BinEx (AND, left, BinEx (LT, exp, r))
            else left

        method find_abs_vals
                (at: abs_type) (solver: yices_smt) (symb_expr: 't expr)
                : (SpinIr.var * int) list list =
            let used = expr_used_vars symb_expr in
            let n_used = List.length used in
            if n_used > 2
            (* NOTE: nothing prevents us from handling multiple variables *)
            (* if anybody needs it, remove the condition and check if it works *)
            then raise (Abstraction_error
                (sprintf "Expression %s has %d variables, we handle 1 or 2"
                    (expr_s symb_expr) n_used))
            else
            (* enumerate all possible abstract tuples of size n_used that have
               a concretization satisfying symb_expr *)
            begin
                let put_interval_constraint var (i, l, r) =
                    solver#append_assert (expr_to_smt (BinEx (GE, Var var, l)));
                    if not_nop r
                    then solver#append_assert (expr_to_smt (BinEx (LT, Var var, r)))
                in
                solver#push_ctx;
                let has_concretization intervals =
                    solver#push_ctx;
                    List.iter2 put_interval_constraint used intervals;
                    let expr_to_check =
                        if (at = ExistAbs) then symb_expr else UnEx(NEG, symb_expr) in
                    solver#append_assert (expr_to_smt expr_to_check);
                    let result = solver#check in
                    solver#pop_ctx;
                    if (at = ExistAbs) then result else (not result)
                in
                let all_interval_tuples =
                    (Accums.mk_product cond_intervals n_used) in
                let matching_interval_tuples =
                    List.filter has_concretization all_interval_tuples in
                let mk_var_val var (abs_val, _, _) = (var, abs_val) in
                solver#pop_ctx;
                List.map
                    (fun intervals -> List.map2 mk_var_val used intervals)
                    matching_interval_tuples
            end

        (*
          distribute n abstract values x_i over the abstract domain s.t.
          sum_{i=1}^n \gamma(x_i) = num_active_processes
         *)
        method scatter_abs_vals (solver: yices_smt)
                (num_expr: 't expr) (n: int) : int list list =
            if n > 4 (* the magic number which means explosion of variants *)
            then raise (Abstraction_error "scatter_abs_vals for n > 4 (A LOT!)");
            
            let combinations = (Accums.mk_product cond_intervals n) in
            let sat_triples_list = List.filter
                (fun comb ->
                    solver#push_ctx;
                    let vars = List.map
                        (fun i -> (new var (sprintf "_a%d" i))) (range 0 n) in
                    List.iter solver#append_var_def vars;
                    List.iter2
                        (fun v (i, l, r) ->
                            solver#append_assert
                                (expr_to_smt (BinEx (GE, Var v, l)));
                            if not_nop r
                            then solver#append_assert
                                (expr_to_smt (BinEx (LT, Var v, r)));
                        ) vars comb;
                    let sum = List.fold_left
                        (fun e v ->
                            if is_nop e then Var v else BinEx (PLUS, Var v, e)
                        ) (Nop "") vars in
                    let sum_eq = BinEx (EQ, num_expr, sum) in
                    solver#append_assert (expr_to_smt sum_eq);
                    let exists_concrete = solver#check in
                    solver#pop_ctx;
                    exists_concrete
                ) combinations in
            let extr_num triples = List.map (fun (i, _, _) -> i) triples in
            List.map extr_num sat_triples_list
       end
;;

let create conds = new pia_domain conds

