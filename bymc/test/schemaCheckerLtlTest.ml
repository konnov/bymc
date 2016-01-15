open OUnit
open Printf

open Accums
open Spin
open SpinIr
open SpinIrImp
open SymbSkel

open SchemaSmt
open SchemaCheckerLtl

let keep x = BinEx (EQ, UnEx (NEXT, Var x), Var x)

let asgn l e = BinEx (EQ, UnEx (NEXT, Var l), e)

let sum v i = BinEx (PLUS, Var v, IntConst i)

let mk_rule src dst guard act = { Sk.src; Sk.dst; Sk.guard; Sk.act }

let declare_parameters sk tt =
    let append_var v = !(SmtTest.solver)#append_var_def v (tt#get_type v) in
    List.iter append_var sk.Sk.params;
    let append_expr e = ignore (!(SmtTest.solver)#append_expr e) in
    List.iter append_expr sk.Sk.assumes


let pad_list lst len desired_len =
    if len < desired_len
    then lst @ (BatList.make (desired_len - len) "()")
    else lst


(*
  Create a symbolic skeleton of the reliable broadcast (STRB).
  *)
let prepare_strb () =
    let tt = new data_type_tab in
    let pc = new_var "pc" in
    let nlocs = 4 in
    tt#set_type pc (mk_int_range 0 (nlocs + 1));
    let x, n, t, f = new_var "x", new_var "n", new_var "t", new_var "f" in
    n#set_symbolic; t#set_symbolic; f#set_symbolic;
    List.iter
        (fun v -> tt#set_type v (new data_type SpinTypes.TUNSIGNED))
        [x; n; t; f];
    let add_loc map i =
        let loc = new_var (sprintf "loc%d" i) in
        IntMap.add i loc map
    in
    let loc_map = List.fold_left add_loc IntMap.empty (range 0 (nlocs + 1)) in
    let mk_eq loc_map loc_no e =
        BinEx (EQ, Var (IntMap.find loc_no loc_map), e)
    in
    let g1 = (* x >= t + 1 - f *)
        BinEx (GE, Var x,
            BinEx (MINUS,
                    (BinEx (PLUS, IntConst 1, Var t)),
                    Var f))
    in
    let g2 = (* x >= n - t - f *)
        BinEx (GE, Var x,
            BinEx (MINUS,
                    BinEx (MINUS, Var n, Var t),
                    Var f))
    in
    let sk = {
        Sk.name = "asyn-agreement";
        Sk.nlocs = nlocs; Sk.locs = [ [0]; [1]; [2]; [3]; [4] ];
        Sk.locals = [ pc ]; Sk.shared = [ x ]; Sk.params = [ n; t; f ];
        Sk.nrules = 4;
        Sk.rules = [
            mk_rule 1 2 (IntConst 1) [ asgn x (sum x 1) ];
            mk_rule 0 2 g1 [ asgn x (sum x 1) ];
            mk_rule 0 3 g2 [ asgn x (sum x 1) ];
            mk_rule 2 3 g2 [ keep x ];
        ];
        Sk.inits = [
            BinEx (EQ, Var x, IntConst 0);
            mk_eq loc_map 0 (BinEx (MINUS, Var n, Var f));
            mk_eq loc_map 1 (IntConst 0);
            mk_eq loc_map 2 (IntConst 0);
            mk_eq loc_map 3 (IntConst 0);
        ];
        Sk.loc_vars = loc_map;
        Sk.assumes = [
            BinEx (GT, Var n, BinEx (MULT, IntConst 3, Var t));
            BinEx (GE, Var t, Var f);
            BinEx (GE, Var f, IntConst 0);
        ];
    }
    in
    declare_parameters sk tt;
    SymbSkel.optimize_guards sk

(*
  Create a symbolic skeleton. This is in fact the example that appeared in our CAV'15 paper.
  *)
let prepare_aba () =
    let tt = new data_type_tab in
    let pc = new_var "pc" in
    let nlocs = 5 in
    tt#set_type pc (mk_int_range 0 (nlocs + 1));
    let x, y, n, t, f = new_var "x", new_var "y", new_var "n", new_var "t", new_var "f" in
    n#set_symbolic; t#set_symbolic; f#set_symbolic;
    List.iter
        (fun v -> tt#set_type v (new data_type SpinTypes.TUNSIGNED))
        [x; y; n; t; f];
    let add_loc map i =
        let loc = new_var (sprintf "loc%d" i) in
        IntMap.add i loc map
    in
    let loc_map = List.fold_left add_loc IntMap.empty (range 0 (nlocs + 1)) in
    let mk_eq loc_map loc_no e =
        BinEx (EQ, Var (IntMap.find loc_no loc_map), e)
    in
    let g1 = (* x >= (n + t) / 2 + 1 - f  (rounding up is omitted) *)
        BinEx (GE, Var x,
            BinEx (MINUS,
                BinEx (PLUS,
                    IntConst 1,
                    BinEx (DIV, (BinEx (MINUS, Var n, Var t)), IntConst 2)),
                Var f))
    in
    let g2 = (* y >= t + 1 -f *)
        BinEx (GE, Var y, BinEx (MINUS, BinEx (PLUS, Var t, IntConst 1), Var f))
    in
    let g3 = (* y >= 2t + 1 -f *)
        BinEx (GE, Var y,
            BinEx (MINUS,
                BinEx (PLUS, BinEx (MULT, IntConst 2, Var t), IntConst 1), Var f))
    in
    let sk = {
        Sk.name = "asyn-agreement";
        Sk.nlocs = nlocs; Sk.locs = [ [0]; [1]; [2]; [3]; [4] ];
        Sk.locals = [ pc ]; Sk.shared = [ x; y ]; Sk.params = [ n; t; f ];
        Sk.nrules = 6;
        Sk.rules = [
            mk_rule 1 2 (IntConst 1) [ asgn x (sum x 1); keep y ];
            mk_rule 0 1 g1 [ asgn x (sum x 1); keep y ];
            mk_rule 0 1 g2 [ asgn x (sum x 1); keep y ];
            mk_rule 2 3 g1 [ keep x; asgn y (sum y 1) ];
            mk_rule 2 3 g2 [ keep x; asgn y (sum y 1) ];
            mk_rule 3 4 g3 [ keep x; keep y ];
        ];
        Sk.inits = [
            BinEx (EQ, Var x, IntConst 0);
            BinEx (EQ, Var y, IntConst 0);
            mk_eq loc_map 0 (BinEx (MINUS, Var n, Var f));
            mk_eq loc_map 1 (IntConst 0);
            mk_eq loc_map 2 (IntConst 0);
            mk_eq loc_map 3 (IntConst 0);
            mk_eq loc_map 4 (IntConst 0);
        ];
        Sk.loc_vars = loc_map;
        Sk.assumes = [
            BinEx (GT, Var n, BinEx (MULT, IntConst 3, Var t));
            BinEx (GE, Var t, Var f);
            BinEx (GE, Var f, IntConst 0);
        ];
    }
    in
    declare_parameters sk tt;
    SymbSkel.optimize_guards sk


type frame_stack_elem_t =
    | Frame of F.frame_t    (* just a frame *)
    | Node of int           (* a node marker *)
    | Context of int        (* a context marker *)


(**
 A tactic that does not nothing but records the executed methods.
 It is a stripped version of SchemaChecker.tree_tac_t
 *)
class mock_tac_t =
    object(self)
        inherit SchemaSmt.tac_t

        val mutable m_frames = []       (** the frame stack *)
        val mutable m_call_stack = []   (** we record the method calls here *)

        (** get the history of calls collected so far *)
        method get_call_history =
            List.rev m_call_stack

        method top =
            let rec find = function
                | (Frame f) :: _ -> f
                | _ :: tl -> find tl
                | [] -> raise (Failure "Frame stack is empty")
            in
            find m_frames

        method frame_hist =
            let m l = function
                | Frame f -> f :: l
                | _ -> l
            in
            List.fold_left m [] (List.rev m_frames)
 
        method private top2 =
            let rec find = function
                | (Frame f) :: tl -> f, tl
                | _ :: tl -> find tl
                | [] -> raise (Failure "Frame stack is empty")
            in
            let top, tl = find m_frames in
            let prev, _ = find tl in
            top, prev

        method push_frame f =
            m_frames <- (Frame f) :: m_frames

        method assert_top _ = ()

        method assert_top2 _ = ()

        method enter_node tp =
            let tag =
                sprintf "(enter_node %s)"
                    (if tp = Leaf then "Leaf" else "Intermediate")
            in
            m_call_stack <- tag :: m_call_stack

        method leave_node tp =
            let tag =
                sprintf "(leave_node %s)"
                    (if tp = Leaf then "Leaf" else "Intermediate")
            in
            m_call_stack <- tag :: m_call_stack

        method check_property exp _ =
            let tag = sprintf "(check_property %s _)" (SpinIrImp.expr_s exp) in
            m_call_stack <- tag :: m_call_stack;
            false (* no bug found *)

        method enter_context =
            m_call_stack <- "(enter_context)" :: m_call_stack

        method leave_context =
            m_call_stack <- "(leave_context)" :: m_call_stack

        method push_rule _ _ rule_no =
            let tag = sprintf "(push_rule _ _ %d)" rule_no in
            m_call_stack <- tag :: m_call_stack
    end


let gen_and_check_schemas_on_the_fly_strb _ =
    let sk = prepare_strb () in
    let deps = PorBounds.compute_deps ~against_only:false !SmtTest.solver sk in
    let tac = new mock_tac_t in
    let bad_form = BinEx (GT, IntConst 2, IntConst 1) in
    let result =
        SchemaCheckerLtl.gen_and_check_schemas_on_the_fly
            !SmtTest.solver sk bad_form deps (tac :> tac_t) in
    assert_equal false result.m_is_err_found
        ~msg:"Expected no errors, found one";

    let hist = tac#get_call_history in
    let check_prop = sprintf "(check_property %s _)" (SpinIrImp.expr_s bad_form) in
    let expected_hist = [
        (* the only path *)
        "(enter_context)";
        "(enter_node Intermediate)";
        "(push_rule _ _ 0)";
        check_prop;
        "(enter_context)";
        "(push_rule _ _ 0)"; (* enables g1 *)
        "(enter_node Intermediate)";
        "(push_rule _ _ 0)"; "(push_rule _ _ 1)";
        check_prop;
        "(enter_context)";
        "(push_rule _ _ 0)"; "(push_rule _ _ 1)"; (* enables g2 *)
        "(enter_node Leaf)";
        "(push_rule _ _ 0)"; "(push_rule _ _ 1)";
        "(push_rule _ _ 2)"; "(push_rule _ _ 3)";
        check_prop;
        "(leave_node Leaf)";
        "(leave_context)";
        "(leave_node Intermediate)";
        "(leave_context)";
        "(leave_node Intermediate)";
        "(leave_context)";
    ] in
    (* pad the histories *)
    let nexpected, nfound = List.length expected_hist, List.length hist in
    let expected_hist = pad_list expected_hist nexpected nfound in
    let hist = pad_list hist nfound nexpected in
    let pp a b = sprintf "    %-30s ----    %-30s" a b in
    assert_equal expected_hist hist
        ~msg:("The histories do not match (expected ---- encountered):\n"
            ^ (str_join "\n" (List.map2 pp expected_hist hist)))


let gen_and_check_schemas_on_the_fly_aba _ =
    let sk = prepare_aba () in
    let deps = PorBounds.compute_deps ~against_only:false !SmtTest.solver sk in
    let tac = new mock_tac_t in
    let bad_form = BinEx (GT, IntConst 2, IntConst 1) in
    let result =
        SchemaCheckerLtl.gen_and_check_schemas_on_the_fly
            !SmtTest.solver sk bad_form deps (tac :> tac_t) in
    assert_equal false result.m_is_err_found
        ~msg:"Expected no errors, found one";

    let hist = tac#get_call_history in
    let check_prop = sprintf "(check_property %s _)" (SpinIrImp.expr_s bad_form) in
    let expected_hist = [
        (* the first path *)
        "(enter_context)";
        "(enter_node Intermediate)";
        "(push_rule _ _ 0)";
        check_prop;
        "(enter_context)";
        "(push_rule _ _ 0)"; (* enables g1 *)
        "(enter_node Intermediate)";
        "(push_rule _ _ 1)"; "(push_rule _ _ 0)"; "(push_rule _ _ 3)";
        check_prop;
        "(enter_context)";
        "(push_rule _ _ 1)"; "(push_rule _ _ 0)"; "(push_rule _ _ 3)"; (* enables g2 *)
        "(enter_node Intermediate)";
        "(push_rule _ _ 1)"; "(push_rule _ _ 2)";
        "(push_rule _ _ 0)"; "(push_rule _ _ 4)"; "(push_rule _ _ 3)";
        check_prop;
        "(enter_context)";
        "(push_rule _ _ 1)"; "(push_rule _ _ 2)";
        "(push_rule _ _ 0)"; "(push_rule _ _ 4)"; "(push_rule _ _ 3)"; (* enables g3 *)
        "(enter_node Leaf)";
        "(push_rule _ _ 1)"; "(push_rule _ _ 2)"; "(push_rule _ _ 0)";
        "(push_rule _ _ 4)"; "(push_rule _ _ 3)"; "(push_rule _ _ 5)";
        check_prop;
        "(leave_node Leaf)";
        "(leave_context)";
        "(leave_node Intermediate)";
        "(leave_context)";
        "(leave_node Intermediate)";
        "(leave_context)";
        "(leave_node Intermediate)";
        "(leave_context)";
        (* the second path *)
        "(enter_context)";
        "(enter_node Intermediate)";
        "(push_rule _ _ 0)";
        check_prop;
        "(enter_context)";
        "(push_rule _ _ 0)"; (* enables g2 *)
        "(enter_node Intermediate)";
        "(push_rule _ _ 2)"; "(push_rule _ _ 0)"; "(push_rule _ _ 4)";
        check_prop;
        "(enter_context)";
        "(push_rule _ _ 2)"; "(push_rule _ _ 0)"; "(push_rule _ _ 4)"; (* enables g3 *)
        "(enter_node Intermediate)";
        "(push_rule _ _ 2)"; "(push_rule _ _ 0)";
        "(push_rule _ _ 4)"; "(push_rule _ _ 5)"; (* enables g1 *)
        check_prop;
        "(enter_context)";
        "(push_rule _ _ 2)"; "(push_rule _ _ 0)";
        "(push_rule _ _ 4)"; "(push_rule _ _ 5)"; (* enables g1 *)
        "(enter_node Leaf)";
        "(push_rule _ _ 1)"; "(push_rule _ _ 2)"; "(push_rule _ _ 0)";
        "(push_rule _ _ 4)"; "(push_rule _ _ 3)"; "(push_rule _ _ 5)";
        check_prop;
        "(leave_node Leaf)";
        "(leave_context)";
        "(leave_node Intermediate)";
        "(leave_context)";
        "(leave_node Intermediate)";
        "(leave_context)";
        "(leave_node Intermediate)";
        "(leave_context)";
        (* the third path *)
        "(enter_context)";
        "(enter_node Intermediate)";
        "(push_rule _ _ 0)";
        check_prop;
        "(enter_context)";
        "(push_rule _ _ 0)"; (* enables g2 *)
        "(enter_node Intermediate)";
        "(push_rule _ _ 2)"; "(push_rule _ _ 0)"; "(push_rule _ _ 4)";
        check_prop;
        "(enter_context)";
        "(push_rule _ _ 2)"; "(push_rule _ _ 0)"; "(push_rule _ _ 4)"; (* enables g1 *)
        "(enter_node Intermediate)";
        "(push_rule _ _ 1)"; "(push_rule _ _ 2)";
        "(push_rule _ _ 0)"; "(push_rule _ _ 4)"; "(push_rule _ _ 3)";
        check_prop;
        "(enter_context)";
        "(push_rule _ _ 1)"; "(push_rule _ _ 2)";
        "(push_rule _ _ 0)"; "(push_rule _ _ 4)"; "(push_rule _ _ 3)"; (* enables g3 *)
        "(enter_node Leaf)";
        "(push_rule _ _ 1)"; "(push_rule _ _ 2)"; "(push_rule _ _ 0)";
        "(push_rule _ _ 4)"; "(push_rule _ _ 3)"; "(push_rule _ _ 5)";
        check_prop;
        "(leave_node Leaf)";
        "(leave_context)";
        "(leave_node Intermediate)";
        "(leave_context)";
        "(leave_node Intermediate)";
        "(leave_context)";
        "(leave_node Intermediate)";
        "(leave_context)";
    ] in
    (* pad the histories *)
    let nexpected, nfound = List.length expected_hist, List.length hist in
    let expected_hist = pad_list expected_hist nexpected nfound in
    let hist = pad_list hist nfound nexpected in
    let pp a b = sprintf "    %-30s ----    %-30s" a b in
    assert_equal expected_hist hist
        ~msg:("The histories do not match (expected ---- encountered):\n"
            ^ (str_join "\n" (List.map2 pp expected_hist hist)))


let to_utl_corr _ =
    let sk = prepare_strb () in
    let get_loc i = Var (IntMap.find i sk.Sk.loc_vars) in
    let eq0 i = BinEx (EQ, get_loc i, IntConst 0) in
    let all_at_loc1 =
        list_to_binex AND [eq0 0; eq0 2; eq0 3; eq0 4]
    in
    let ltl_form =
        BinEx (AND, all_at_loc1, (UnEx (ALWAYS, eq0 4)))
    in
    let expected_utl =
        TL_and [TL_p (And_Keq0 [4; 3; 0; 2]); TL_G (TL_p (And_Keq0 [4]))]
    in
    let result_utl = SchemaCheckerLtl.to_utl sk ltl_form in
    assert_equal expected_utl result_utl
        ~msg:(sprintf "Expected %s, found %s"
            (utl_spec_s expected_utl) (utl_spec_s result_utl))


let suite = "schemaCheckerLtl-suite" >:::
    [
        "compute_schema_tree_on_the_fly_strb"
            >::(bracket SmtTest.setup_smt2
                gen_and_check_schemas_on_the_fly_strb SmtTest.shutdown_smt2);
        "compute_schema_tree_on_the_fly_aba"
            >::(bracket SmtTest.setup_smt2
                gen_and_check_schemas_on_the_fly_aba SmtTest.shutdown_smt2);
        "to_utl_corr"
            >::(bracket SmtTest.setup_smt2 to_utl_corr SmtTest.shutdown_smt2);
    ]

