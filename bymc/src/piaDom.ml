open Printf

open AbsBasics
open Spin
open SpinIr
open SpinIrImp
open Smt
open VarRole

open Accums
open Debug

exception Found of int

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
                        ignore (solver#append_expr (BinEx (GE, symb_expr, l)));
                        if not_nop r
                        then ignore
                            (solver#append_expr (BinEx (LT, symb_expr, r)));
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
            let eq (a, _, _) = (a = abs_val) in
            let (_, l, r) = List.find eq cond_intervals in
            match l, r with
            | Const a, Const b ->
                if b = a + 1
                then BinEx (EQ, exp, Const a)
                else BinEx (AND, BinEx (GE, exp, l), BinEx (LT, exp, r))

            | _, Nop _ ->
                BinEx (GE, exp, l) 

            | _, _ ->
                BinEx (AND, BinEx (GE, exp, l), BinEx (LT, exp, r))

        method find_abs_vals
                (at: abs_type) (solver: yices_smt) (symb_expr: 't expr)
                : (SpinIr.var * int) list list =
            let used = expr_used_vars symb_expr in
            let n_used = List.length used in
            (* enumerate all possible abstract tuples of size n_used that have
               a concretization satisfying symb_expr *)
            let put_interval_constraint var (i, l, r) =
                ignore (solver#append_expr (BinEx (GE, Var var, l)));
                if not_nop r
                then ignore (solver#append_expr (BinEx (LT, Var var, r)))
            in
            let has_concretization intervals =
                solver#push_ctx;
                List.iter2 put_interval_constraint used intervals;
                let expr_to_check =
                    if (at = ExistAbs)
                    then symb_expr
                    else UnEx(NEG, symb_expr)
                in
                ignore (solver#append_expr expr_to_check);
                let result = solver#check in
                solver#pop_ctx;
                if (at = ExistAbs) then result else (not result)
            in
            solver#push_ctx;
            let all_interval_tuples =
                (Accums.mk_product cond_intervals n_used) in
            let matching_interval_tuples =
                List.filter has_concretization all_interval_tuples in
            let mk_var_val var (abs_val, _, _) = (var, abs_val) in
            solver#pop_ctx;
            List.map
                (fun intervals -> List.map2 mk_var_val used intervals)
                matching_interval_tuples

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
                        (fun i -> (new_var (sprintf "_a%d" i))) (range 0 n) in
                    let append_def v =
                        solver#append_var_def v (new data_type SpinTypes.TINT)
                    in
                    List.iter append_def vars;
                    List.iter2
                        (fun v (i, l, r) ->
                            ignore (solver#append_expr (BinEx (GE, Var v, l)));
                            if not_nop r
                            then ignore (solver#append_expr (BinEx (LT, Var v, r)));
                        ) vars comb;
                    let sum = List.fold_left
                        (fun e v ->
                            if is_nop e then Var v else BinEx (PLUS, Var v, e)
                        ) (Nop "") vars in
                    let sum_eq = BinEx (EQ, num_expr, sum) in
                    ignore (solver#append_expr sum_eq);
                    let exists_concrete = solver#check in
                    solver#pop_ctx;
                    exists_concrete
                ) combinations in
            let extr_num triples = List.map (fun (i, _, _) -> i) triples in
            List.map extr_num sat_triples_list
       end


exception Skeleton_not_supported of string

let identify_conditions var_roles stmts =
    let is_symb_expr e = not (expr_exists not_symbolic e) in
    let thresh_lt l r =
        let ls = is_symb_expr l and rs = is_symb_expr r in
        (if ls then [l] else []) @ (if rs then [r] else [])
    in
    let thresh_le l r =
        let ls = is_symb_expr l and rs = is_symb_expr r in
        if ls && not rs (* N <= x, i.e., x >= N *)
        then [l]
        else if rs && not ls
        then [BinEx (PLUS, Const 1, r)] (* x <= N means N + 1 is the threshold *)
        else [] (* it is either a constant expression, or a general one *)
    in

    let rec on_expr e =
        match e with
        | BinEx(AND, l, r) -> List.append (on_expr l) (on_expr r)
        | BinEx(OR, l, r)  -> List.append (on_expr l) (on_expr r)
        | UnEx(NEG, l)     -> on_expr l
        | BinEx(LT, l, r) -> thresh_lt l r
        | BinEx(GE, l, r) -> thresh_le r l
        | BinEx(LE, l, r) -> thresh_le l r
        | BinEx(GT, l, r) -> thresh_lt r l
        | _ -> []
    in
    let tab = Hashtbl.create 10 in
    let add_on_demand c =
        let s = expr_s c in
        if not (Hashtbl.mem tab s) then Hashtbl.replace tab s c
    in
    let rec for_stmts = function
        | Expr (_, e) -> List.iter add_on_demand (on_expr e)
        | _ -> ()
    in
    add_on_demand (Const 0);
    add_on_demand (Const 1);
    List.iter for_stmts stmts;
    hashtbl_vals tab


let sort_thresholds solver conds =
    let id_map = Hashtbl.create 10 in
    List.iter (fun c -> Hashtbl.add id_map c (Hashtbl.length id_map)) conds;
    solver#push_ctx;
    let cmp_tbl = Hashtbl.create 10 in
    let compare op c1 c2 =
        if c1 <> c2
        then begin
            let i1 = Hashtbl.find id_map c1
                and i2 = Hashtbl.find id_map c2 in
            let asrt = UnEx (NEG, BinEx (op, c1, c2)) in
            solver#push_ctx;
            ignore (solver#append_expr asrt);
            let res = not solver#check in
            if res then (Hashtbl.add cmp_tbl (i1, i2) true);
            solver#pop_ctx; 
            res
        end
        else false
    in
    let lt c1 c2 = let _ = compare LT c1 c2 in () in
    List.iter (fun c1 -> List.iter (lt c1) conds) conds;
    let rm_tbl = Hashtbl.create 10 in
    let check_ord c1 c2 = 
        let i1 = (Hashtbl.find id_map c1) and i2 = (Hashtbl.find id_map c2) in
        if i1 <> i2
        then if not (Hashtbl.mem cmp_tbl (i1, i2))
            && not (Hashtbl.mem cmp_tbl (i2, i1))
        then begin
            let m =
                sprintf "No strict order for %s and %s" (expr_s c1) (expr_s c2)
            in
            if compare LE c1 c2 && compare LE c2 c1
            then begin
                log INFO (sprintf "    %s is equivalent to %s\n"
                    (expr_s c1) (expr_s c2));
                Hashtbl.replace rm_tbl c2 true
            end else if compare LE c1 c2
            then begin
                log INFO (sprintf "    %s <= %s\n"
                    (expr_s c1) (expr_s c2));
                (* DEPRECATED: Hashtbl.replace rm_tbl c2 true *)
            end else if compare LE c2 c1
            then begin
                log INFO (sprintf "    %s <= %s\n"
                    (expr_s c2) (expr_s c1));
                (* DEPRECATED: Hashtbl.replace rm_tbl c1 true *)
            end else
            raise (Abstraction_error m)
        end
    in
    List.iter (fun c1 -> List.iter (check_ord c1) conds) conds;
    solver#pop_ctx;
    let conds = List.filter (fun c -> not (Hashtbl.mem rm_tbl c)) conds in
    let cmp_using_tbl c1 c2 =
        let i1 = (Hashtbl.find id_map c1) and i2 = (Hashtbl.find id_map c2) in
        if c1 = c2 then 0 else if (Hashtbl.mem cmp_tbl (i1, i2)) then -1 else 1
    in
    List.sort cmp_using_tbl conds


let create solver var_roles prog =
    log INFO "> Extracting the abstract domain...";
    let collect_stmts l p = p#get_stmts @ l in
    let all_stmts = List.fold_left collect_stmts [] (Program.get_procs prog)
    in
    let conds = identify_conditions var_roles (mir_to_lir all_stmts) in
    let sorted_conds = sort_thresholds solver conds in
    let dom = new pia_domain sorted_conds in
    dom#print;
    flush stdout;
    dom

