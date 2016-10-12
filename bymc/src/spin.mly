/* OCaml version of the (extended) Promela parser            */
/* Adapted from the original yacc grammar of Spin 6.0.1,     */
/* which can be found in spin.mly                            */
/*                                                           */
/* This grammar also contains parts for parsing threshold    */
/* automata. Since ocamlyacc does not support well several   */
/* grammars in the same project, we had to merge these two   */
/* grammars together.                                        */
/*                                                           */
/* TODO: use menhir for better error reporting and decoupling */
/* the grammars.                                             */
/*                                                           */
/* Igor Konnov 2012, 2016                                    */


%{

open Printf

open Lexing
open SpinIr
open SpinlexGlue
open SpinParserState

let met_else = ref false
let fwd_labels = Hashtbl.create 10
let lab_stack = ref []

let push_new_labs () =
    let e = mk_uniq_label () in (* one label for entry to do *)
    let b = mk_uniq_label () in (* one label to break from do/if *)
    lab_stack := (e, b) :: !lab_stack


let pop_labs () = lab_stack := List.tl !lab_stack 

let top_labs () = List.hd !lab_stack

(* it uses tokens, so we cannot move it outside *)
let rec is_expr_symbolic e =
    match e with
    | IntConst _ -> true
    | Var v -> v#is_symbolic
    | UnEx (op, se) -> op = UMIN && is_expr_symbolic se
    | BinEx (op, le, re) ->
        (List.mem op [PLUS; MINUS; MULT; DIV; MOD])
            && (is_expr_symbolic le) && (is_expr_symbolic re)
    | _ -> false


let find_or_declare_next v =
    if not (v#has_flag HNext)
    then v#add_flag HNext;

    let new_name = v#get_name ^ "_X" in
    try ((top_scope ())#lookup new_name)#as_var
    with Symbol_not_found _ ->
        let nv = v#fresh_copy new_name in
        (top_scope ())#add_symb nv#get_name (nv :> symb);
        nv


let declare_next stmts =
    let each_decl (lst, prev_nexts) = function
    | MDecl (_, v, e) as d ->
            if not (v#has_flag HNext)
            then (d :: lst, prev_nexts)
            else begin
                let nv = find_or_declare_next v in
                let nflags = List.filter (fun f -> f <> HNext) v#get_flags in
                v#set_flags nflags; (* remove HNext *)
                nv#set_flags nflags; (* remove HNext *)
                let tp = (type_tab ())#get_type v in
                (type_tab ())#set_type nv tp;
                let pn = (v, nv) in
                ((MDecl (fresh_id (), nv, e)) :: d :: lst, pn :: prev_nexts)
            end

    | _ as e ->
            (e :: lst, prev_nexts)
    in
    let seq, pns = List.fold_left each_decl ([], []) stmts in
    let make_after (prev, next) =
        MExpr (fresh_id (), BinEx (ASGN, Var prev, Var next)) in
    let make_zero (_, next) =
        MExpr (fresh_id (), BinEx (ASGN, Var next, IntConst 0)) in
    let make_before (prev, next) =
        MExpr (fresh_id (), BinEx (ASGN, Var next, Var prev)) in
    let before = List.map make_before pns in
    let after = List.map make_after pns in
    let zero = List.map make_zero pns in
    let rec on_seq = function
        | [] -> []

        | (MIf (id, opts)) :: tl ->
            (MIf (id, List.map each_opt opts)) :: (on_seq tl)

        | (MD_step (id, seq)) :: tl ->
            (MD_step (id, on_seq seq)) :: (on_seq tl)

        | (MAtomic (id, seq)) :: tl ->
            (MAtomic (id, before @ seq @ after @ zero)) :: (on_seq tl)

        | e :: tl -> e :: (on_seq tl)

    and each_opt = function
        | MOptGuarded seq -> MOptGuarded (on_seq seq)
        | MOptElse seq -> MOptElse (on_seq seq)
    in
    on_seq (List.rev seq)


let curr_pos () =
    let p = Parsing.symbol_start_pos () in
    let fname = if p.pos_fname != "" then p.pos_fname else "<filename>" in
    let col = max (p.pos_cnum - p.pos_bol + 1) 1 in
    (fname, p.pos_lnum, col)


let parse_error s =
    let f, l, c = curr_pos() in
    Printf.printf "%s:%d,%d %s\n" f l c s;
    inc_err_cnt ()


let fatal msg payload =
    let f, l, c = curr_pos() in
    raise (Failure (Printf.sprintf "%s:%d,%d %s %s\n" f l c msg payload))

%}

%token	ASSERT PRINT PRINTM
%token	C_CODE C_DECL C_EXPR C_STATE C_TRACK
%token	RUN LEN ENABLED EVAL PC_VAL
%token	TYPEDEF MTYPE INLINE LABEL OF
%token	GOTO BREAK ELSE SEMI
%token	IF FI DO OD FOR SELECT IN SEP DOTDOT
%token	ATOMIC NON_ATOMIC D_STEP UNLESS
%token  TIMEOUT NONPROGRESS
%token	ACTIVE PROCTYPE D_PROCTYPE
%token	HIDDEN SHOW ISLOCAL
%token	PRIORITY PROVIDED
%token	FULL EMPTY NFULL NEMPTY
%token	<int> CONST                 /* val */
%token  <SpinTypes.var_type> TYPE
%token  <SpinTypes.xu_type> XU			    /* val */
%token	<string> NAME
%token  <string> UNAME
%token  <string> PNAME
%token  <string> INAME		        /* sym */
%token  <string> FNAME		        /* atomic proposition name */
%token	<string> STRING
%token  CLAIM TRACE INIT	LTL	/* sym */
%token  NE EQ LT GT LE GE OR AND BITNOT BITOR BITXOR BITAND ASGN
%token  MULT PLUS MINUS DIV MOD DECR INCR
%token  LSHIFT RSHIFT
%token  COLON DOT COMMA LPAREN RPAREN LBRACE RBRACE LCURLY RCURLY
%token  O_SND SND RCV R_RCV AT
%token  NEVER NOTRACE TRACE ASSERT
%token	ALWAYS EVENTUALLY		    /* ltl */
%token	UNTIL WEAK_UNTIL RELEASE	/* ltl */
%token	NEXT IMPLIES EQUIV          /* ltl */
%token	PRIME                       /* our extension */
%token  <string * string> DEFINE
%token  <string * string> PRAGMA
%token  <string> INCLUDE
%token  MACRO_IF MACRO_ELSE MACRO_ENDIF
%token  <string> MACRO_IFDEF
%token  <string> MACRO_IFNDEF
%token  <string> MACRO_OTHER
%token  EOF
/* FORSYTE extensions { */
%token  ASSUME SYMBOLIC ALL SOME CARD POR PAND HAVOC
/* FORSYTE extensions } */
/* imaginary tokens not directly used in the grammar, but used in the
   intermediate representations
 */
%token  UMIN NEG VARREF ARR_ACCESS ARR_UPDATE

%right	ASGN
%left	O_SND R_RCV SND RCV
%left	IMPLIES EQUIV			/* ltl */
%left	OR
%left	AND
%left	ALWAYS EVENTUALLY		    /* ltl */
%left	UNTIL WEAK_UNTIL RELEASE	/* ltl */
%right	NEXT				        /* ltl */
%left	BITOR BITXOR BITAND
%left	EQ NE
%left	GT LT GE LE
%left	LSHIFT RSHIFT
%left	PLUS MINUS
%left	MULT DIV MOD
%left	INCR DECR
%right	UMIN BITNOT NEG
%left	DOT
%start program
%type <token SpinIr.prog_unit list * SpinIr.data_type_tab> program
%start expr
%type <token SpinIr.expr> expr
%%

/** PROMELA Grammar Rules **/

program	: units	EOF { ($1, type_tab ()) }
	;

units	: unit      { $1 }
    | units unit    { List.append $1 $2 }
	;

unit	: proc	/* proctype        */    { [Proc $1] }
    | init		/* init            */    { [] }
	| claim		/* never claim        */ { [] }
    | ltl		/* ltl formula        */ { [$1] }
	| events	/* event assertions   */ { [] }
	| one_decl	/* variables, chans   */ { List.map (fun e -> Stmt e) $1 }
	| utype		/* user defined types */ { [] }
	| c_fcts	/* c functions etc.   */ { [] }
	| ns		/* named sequence     */ { [] }
	| SEMI		/* optional separator */ { [] }
    /* FORSYTE extensions */
    | prop_decl /* atomic propositions */ { [Stmt $1] }
	| ASSUME full_expr /* assumptions */
        {
            [Stmt (MAssume (fresh_id (), $2))]
        }
    | PROVIDED NAME LPAREN prargs RPAREN {
        let args = list_to_binex COMMA $4 in
        [Stmt (MExpr (fresh_id (), BinEx (PROVIDED, Var (new_var $2), args)))] }
	| error { fatal "Unexpected top-level statement" ""}
	;

proc	: inst		/* optional instantiator */
	  proctype_name
	  LPAREN decl RPAREN
	  Opt_priority
	  Opt_enabler
	  body	{
                let my_scope = top_scope () in
                let p = new proc my_scope#tab_name $1 in
                let unpack e =
                    match e with    
                    | MDecl (_, v, i) -> v#add_flag HFormalPar; v
                    | _ -> fatal "Not a decl in proctype args" p#get_name
                in
                p#set_args (List.map unpack $4);
                p#set_stmts (declare_next $8);
                p#add_all_symb my_scope#get_symbs;
                pop_scope ();
                Hashtbl.clear fwd_labels;
                p
            }
        ;

proctype_name: PROCTYPE NAME {
        push_scope (new symb_tab $2)
        }
    | D_PROCTYPE NAME {
        push_scope (new symb_tab $2)
        }
    ;

inst	: /* empty */	{ IntConst 0 }
    | ACTIVE	{ IntConst 1 }
    /* FORSYTE extension: any constant + a symbolic arith expression */
    | ACTIVE LBRACE expr RBRACE {
            match $3 with
            | IntConst i -> IntConst i
            | Var v ->
                if v#is_symbolic
                then Var v
                else fatal (sprintf "%s is neither symbolic nor a constant" v#get_name) ""
            | _ -> if is_expr_symbolic $3 then $3 else
                fatal "active [..] must be constant or symbolic" ""
        }
    ;

init	: INIT		    /* { } */
      Opt_priority
      body		        { }
    ;

ltl	: ltl_prefix FNAME ltl_body	{
        set_lexer_normal();
        (* TODO: put it somewhere *)
        Ltl($2, $3)
    }
;

ltl_prefix: LTL
    { set_lexer_ltl() }
;

ltl_body: LCURLY ltl_expr RCURLY { $2 }
    | error		{ fatal "Incorrect inline LTL formula" "" }
    ;

/* this rule is completely different from Spin's ltl_expr  */
ltl_expr:
      LPAREN ltl_expr RPAREN        { $2 }
    | NEG ltl_expr                  { UnEx(NEG, $2) }
    | ltl_expr UNTIL ltl_expr	    { BinEx(UNTIL, $1, $3) }
	| ltl_expr RELEASE ltl_expr	    { BinEx(RELEASE, $1, $3) }
	| ltl_expr WEAK_UNTIL ltl_expr	{ BinEx(WEAK_UNTIL, $1, $3) }
	| ltl_expr IMPLIES ltl_expr     { BinEx(OR, UnEx(NEG, $1), $3) }
	| ltl_expr EQUIV ltl_expr	    { BinEx(EQUIV, $1, $3) }
	| ALWAYS ltl_expr     { UnEx(ALWAYS, $2) }
	| EVENTUALLY ltl_expr { UnEx(EVENTUALLY, $2) }
    | ltl_expr AND ltl_expr         { BinEx(AND, $1, $3) }
    | ltl_expr OR ltl_expr          { BinEx(OR, $1, $3) }
    | FNAME                        
        { let v = new_var $1 in
          (type_tab ())#set_type v (new data_type SpinTypes.TPROPOSITION);
          Var v }
    | FNAME AT FNAME                  { LabelRef($1, $3) }
  /* TODO: implement this later
    | LPAREN expr RPAREN            { }
   */
  /* sorry, next time we support nexttime (hardly ever happens) */
  /*| NEXT ltl_expr       %prec NEG {...} */
	;

claim	: CLAIM	optname	body { }
    ;

optname : /* empty */	{ }
    | NAME		{ }
    ;

events : TRACE	
      body	{ raise (Not_implemented "TRACE")
    }
    ;

utype	: TYPEDEF NAME LCURLY decl_lst LCURLY	{
                raise (Not_implemented "typedef is not supported")
    }
    ;

nm	: NAME			{ }
    | INAME			{ }
    ;

ns	: INLINE nm LPAREN args RPAREN {
                    raise (Not_implemented "inline")
    }
    ;

c_fcts	: ccode			{
                    raise (Not_implemented "c_fcts")
                }
    | cstate {}
    ;

cstate	: C_STATE STRING STRING	{
                 raise (Not_implemented "c_state")
                }
    | C_TRACK STRING STRING {
                 raise (Not_implemented "c_track")
                }
    | C_STATE STRING STRING	STRING {
                 raise (Not_implemented "c_state")
                }
    | C_TRACK STRING STRING STRING {
                 raise (Not_implemented "c_track")
                }
    ;

ccode	: C_CODE {
                 raise (Not_implemented "c_code")
                }
    | C_DECL		{
                 raise (Not_implemented "c_decl")
                }
    ;
cexpr	: C_EXPR	{
                 raise (Not_implemented "c_expr")
                }
    ;

body	: LCURLY sequence OS RCURLY    { $2 }
    ;

sequence: step			{ $1 }
    | sequence MS step	{ List.append $1 $3 }
    ;

step    : one_decl		{ $1 }
    | XU vref_lst		{ raise (Not_implemented "XU vref_lst") }
    | NAME COLON one_decl	{ fatal "label preceding declaration," "" }
    | NAME COLON XU		{ fatal "label predecing xr/xs claim," "" }
    | stmnt			    { $1 }
    | stmnt UNLESS stmnt	{ raise (Not_implemented "unless") }
    ;

vis	: /* empty */	{ HNone }
    | HIDDEN		{ HHide }
    | SHOW			{ HShow }
    | ISLOCAL		{ HTreatLocal }
    | SYMBOLIC      { HSymbolic }
    ;

asgn:	/* empty */ {}
    | ASGN {}
    ;

one_decl: vis TYPE var_list	{
        let fl = $1 and tp = new data_type $2 in
        let add_decl ((v, tp_rhs), init) =
            (* type constraints in the right-hand side *)
            tp#set_nelems tp_rhs#nelems;
            tp#set_nbits tp_rhs#nbits;
            if tp_rhs#nbits > 0
            then tp#set_range 0 (Accums.ipow 2 tp_rhs#nbits);
            v#add_flag fl;
            (type_tab ())#set_type v tp;
            (top_scope ())#add_symb v#get_name (v :> symb);
            MDecl(fresh_id (), v, init)
        in
        List.map add_decl $3
    }
    | vis UNAME var_list	{
                  raise (Not_implemented "variables of user-defined types")
                }
    | vis TYPE asgn LCURLY nlst RCURLY {
                  raise (Not_implemented "mtype = {...}")
                }
    ;

decl_lst: one_decl       	{ $1 }
    | one_decl SEMI
      decl_lst		        { $1 @ $3 }
    ;

decl    : /* empty */		{ [] }
    | decl_lst      	    { $1 }
    ;

vref_lst: varref		    { }
    | varref COMMA vref_lst	{ }
    ;

var_list: ivar              { [$1] }
    | ivar COMMA var_list	{ $1 :: $3 }
    ;

ivar    : vardcl           	{ ($1, Nop "") }
    | vardcl ASGN expr   	{
        ($1, $3)
        }
    | vardcl ASGN ch_init	{
          raise (Not_implemented "var = ch_init")
        }
    ;

ch_init : LBRACE CONST RBRACE OF
      LCURLY typ_list RCURLY	{
                 raise (Not_implemented "channels")
                    }
    ;

vardcl  : NAME {
        let v = new_var $1 in
        v#set_proc_name (top_scope ())#tab_name;
        (v, new data_type SpinTypes.TUNDEF)
        }
    | NAME COLON CONST	{
        let v = new_var $1 in
        v#set_proc_name (top_scope ())#tab_name;
        let tp = new data_type SpinTypes.TUNDEF in
        tp#set_nbits $3;
        (v, tp)
        }
    | NAME LBRACE CONST RBRACE	{
        let v = new_var $1 in
        v#set_proc_name (top_scope ())#tab_name;
        let tp = new data_type SpinTypes.TUNDEF in
        tp#set_nelems $3;
        (v, tp)
        }
    ;

varref	: cmpnd		{ $1 }
    ;

pfld	: NAME {
            try
                ((top_scope ())#lookup $1)#as_var
            with Symbol_not_found _ ->
                (* XXX: check that the current expression can use that *)
                ((spec_scope ())#lookup $1)#as_var
            }
    | NAME LBRACE expr RBRACE
            { raise (Not_implemented
                "Array references, e.g., x[y] are not implemented") }
    ;

cmpnd	: pfld sfld { $1 }
    ;

sfld	: /* empty */		{ }
    | DOT cmpnd %prec DOT	{
         raise (Not_implemented
                "Structure member addressing, e.g., x.y is not implemented")
    ;

stmnt	: Special		{ $1 }
    | Stmnt			{ $1 }
    ;

for_pre : FOR LPAREN varref		{ raise (Not_implemented "for") }
    ;

for_post: LCURLY sequence OS RCURLY { raise (Not_implemented "for") } ;

Special :
    | HAVOC LPAREN varref_or_prime RPAREN { [MHavoc (fresh_id (), $3)]  }
    | varref RCV
      rargs		{ raise (Not_implemented "rcv") }
    | varref SND margs		{ raise (Not_implemented "snd")
                }
    | for_pre COLON expr DOTDOT expr RPAREN
      for_post	{ raise (Not_implemented "for_post") }
    | for_pre IN varref RPAREN
      for_post	{ raise (Not_implemented "for_pre") }
    | SELECT LPAREN varref COLON expr DOTDOT expr RPAREN {
                    raise (Not_implemented "select")
                }
    | if_begin options FI	{
                pop_labs ();                
                met_else := false;
                [ MIf (fresh_id (), $2) ]
          }
    | do_begin 		/* one more rule as ocamlyacc does not support multiple
                       actions like this: { (* pushbreak(); *) } */
          options OD {
                (* use of elab/entry_lab is redundant, but we want
                   if/fi and do/od look similar as some algorithms
                   can cut off gotos at the end of an option *)
                let (_, break_lab) = top_labs ()
                    and entry_lab = mk_uniq_label()
                    and opts = $2 in
                met_else := false;
                let do_s =
                    [MLabel (fresh_id (), sprintf "_lab%d" entry_lab);
                     MIf (fresh_id (), opts);
                     MGoto (fresh_id (), sprintf "_lab%d" entry_lab);
                     MLabel (fresh_id (), sprintf "_lab%d" break_lab)]
                in
                pop_labs ();                
                do_s

                }
    | BREAK     {
                let (_, blab) = top_labs () in
                [MGoto (fresh_id (), sprintf "_lab%d" blab)]
                }
    | GOTO NAME		{
        [MGoto (fresh_id (), $2)]
    }
| NAME COLON stmnt	{
    let label_no =
        try
            let _ = (top_scope ())#lookup $1 in
            fatal "" (sprintf "Label %s redeclared\n" $1)
        with Symbol_not_found _ ->
            if Hashtbl.mem fwd_labels $1
            then Hashtbl.find fwd_labels $1
            else mk_uniq_label ()
    in
    (top_scope ())#add_symb $1 ((new label $1 label_no) :> symb);
    MLabel (fresh_id (), $1) :: $3
    }
;

Stmnt	: varref_or_prime ASGN full_expr	{
                    [MExpr (fresh_id (), BinEx(ASGN, Var $1, $3))]
				}
	| varref INCR		{
                    let v = Var $1 in
                    [MExpr (fresh_id (), BinEx(ASGN, v, BinEx(PLUS, v, IntConst 1)))]
				}
	| varref DECR	{
                    let v = Var $1 in
                    [MExpr (fresh_id (), BinEx(ASGN, v, BinEx(MINUS, v, IntConst 1)))]
				}
	| PRINT	LPAREN STRING prargs RPAREN	{
                    [MPrint (fresh_id (), $3, $4)]
                }
	| PRINTM LPAREN varref RPAREN	{
                    (* do we actually need it? *)
                    raise (Not_implemented "printm")
                }
	| PRINTM LPAREN CONST RPAREN	{
                    raise (Not_implemented "printm")
                }
	| ASSUME full_expr    	{
                    if is_expr_symbolic $2
                    then fatal "active [..] must be constant or symbolic" ""
                    else [MAssume (fresh_id (), $2)] (* FORSYTE ext. *)
                }
	| ASSERT full_expr    	{
                    [MAssert (fresh_id (), $2)]
                }
	| ccode			{ raise (Not_implemented "ccode") }
	| varref R_RCV rargs { raise (Not_implemented "R_RCV") }
	| varref RCV LT rargs GT { raise (Not_implemented "rcv") }
	| varref R_RCV LT rargs GT { raise (Not_implemented "r_rcv") }
	| varref O_SND margs { raise (Not_implemented "o_snd") }
	| full_expr		{ [MExpr (fresh_id (), $1)] }
    | ELSE  		{ met_else := true; [] }
	| ATOMIC   LCURLY sequence OS RCURLY {
              [ MAtomic (fresh_id (), $3) ]
		  }
	| D_STEP LCURLY sequence OS RCURLY {
              [ MD_step (fresh_id (), $3) ]
		  }
	| LCURLY sequence OS RCURLY	{
              $2
	   	  }
	| INAME LPAREN args RPAREN
	  Stmnt			{ raise (Not_implemented "inline") }
	;

if_begin : IF { push_new_labs () }
;

do_begin : DO { push_new_labs () }
;

options : option { [$1] }
    | option options { $1 :: $2 }
	;

option_head : SEP   { met_else := false }
;

option  : option_head
      sequence OS	{
          if !met_else then MOptElse $2 else MOptGuarded $2
      }
	;

OS	: /* empty */ {}
	| SEMI			{ (* redundant semi at end of sequence *) }
	;

MS	: SEMI			{ (* at least one semi-colon *) }
	| MS SEMI		{ (* but more are okay too   *) }
	;

aname	: NAME		{ $1 }
	| PNAME			{ $1 }
	;

/* should we use full_expr here and then check the tree? */
prop_expr   :
      LPAREN prop_expr RPAREN       { $2 }
    | prop_expr AND prop_expr       { BinEx(AND, $1, $3) }
    | prop_expr OR prop_expr        { BinEx(OR, $1, $3) }
    | NEG prop_expr                 { UnEx(NEG, $2) }
    | NAME AT NAME                  { LabelRef ($1, $3) }
	| prop_arith_expr GT prop_arith_expr		{ BinEx(GT, $1, $3) }
	| prop_arith_expr LT prop_arith_expr		{ BinEx(LT, $1, $3) }
	| prop_arith_expr GE prop_arith_expr		{ BinEx(GE, $1, $3) }
	| prop_arith_expr LE prop_arith_expr		{ BinEx(LE, $1, $3) }
	| prop_arith_expr EQ prop_arith_expr		{ BinEx(EQ, $1, $3) }
	| prop_arith_expr NE prop_arith_expr		{ BinEx(NE, $1, $3) }
    ;

prop_arith_expr    : 
	  LPAREN prop_arith_expr RPAREN		{ $2 }
	| prop_arith_expr PLUS prop_arith_expr		{ BinEx(PLUS, $1, $3) }
	| prop_arith_expr MINUS prop_arith_expr		{ BinEx(MINUS, $1, $3) }
	| prop_arith_expr MULT prop_arith_expr		{ BinEx(MULT, $1, $3) }
	| prop_arith_expr DIV prop_arith_expr		{ BinEx(DIV, $1, $3) }
	| CARD LPAREN prop_expr	RPAREN	{ UnEx(CARD, $3) }
    | NAME /* proctype */ COLON NAME
        {
            let v = new_var $3 in
            v#set_proc_name $1;
            Var (v)
        }
	| NAME
        {
            try
                Var ((global_scope ())#find_or_error $1)#as_var
            with Not_found ->
                fatal "prop_arith_expr: " (sprintf "Undefined global variable %s" $1)
        }
	| CONST { IntConst $1 }
    ;

expr    : LPAREN expr RPAREN		{ $2 }
	| expr PLUS expr		{ BinEx(PLUS, $1, $3) }
	| expr MINUS expr		{ BinEx(MINUS, $1, $3) }
	| expr MULT expr		{ BinEx(MULT, $1, $3) }
	| expr DIV expr		    { BinEx(DIV, $1, $3) }
	| expr MOD expr		    { BinEx(MOD, $1, $3) }
	| expr BITAND expr		{ BinEx(BITAND, $1, $3) }
	| expr BITXOR expr		{ BinEx(BITXOR, $1, $3) }
	| expr BITOR expr		{ BinEx(BITOR, $1, $3) }
	| expr GT expr		    { BinEx(GT, $1, $3) }
	| expr LT expr		    { BinEx(LT, $1, $3) }
	| expr GE expr		    { BinEx(GE, $1, $3) }
	| expr LE expr		    { BinEx(LE, $1, $3) }
	| expr EQ expr		    { BinEx(EQ, $1, $3) }
	| expr NE expr		    { BinEx(NE, $1, $3) }
	| expr AND expr		    { BinEx(AND, $1, $3) }
	| expr OR  expr		    { BinEx(OR, $1, $3) }
	| expr LSHIFT expr	    { BinEx(LSHIFT, $1, $3) }
	| expr RSHIFT expr	    { BinEx(RSHIFT, $1, $3) }
	| BITNOT expr		    { UnEx(BITNOT, $2) }
	| MINUS expr %prec UMIN	{ UnEx(UMIN, $2) }
	| NEG expr	            { UnEx(NEG, $2) }
    /* our extensions */
    | ALL LPAREN prop_expr RPAREN { UnEx (ALL, $3)  }
    | SOME LPAREN prop_expr RPAREN { UnEx (SOME, $3)  }

    /* not implemented yet */
	| LPAREN expr SEMI expr COLON expr RPAREN {
                  raise (Not_implemented "ternary operator")
				}

	| RUN aname	LPAREN args RPAREN
	  Opt_priority		{ raise (Not_implemented "run") }
	| LEN LPAREN varref RPAREN	{ raise (Not_implemented "len") }
	| ENABLED LPAREN expr RPAREN { raise (Not_implemented "enabled") }
	| varref RCV LBRACE rargs RBRACE { raise (Not_implemented "rcv") }
	| varref R_RCV LBRACE rargs RBRACE
        { raise (Not_implemented "r_rcv") }
    | varref_or_prime   { Var $1 }
	| cexpr			{raise (Not_implemented "cexpr") }
	| CONST 	{ IntConst $1 }
	| TIMEOUT		{ raise (Not_implemented "timeout") }
	| NONPROGRESS		{ raise (Not_implemented "nonprogress") }
	| PC_VAL LPAREN expr RPAREN	{ raise (Not_implemented "pc_value") }
	| PNAME LBRACE expr RBRACE AT NAME
	  			{  raise (Not_implemented "PNAME operations") }
	| PNAME LBRACE expr RBRACE COLON pfld
	  			{  raise (Not_implemented "PNAME operations") }
	| PNAME AT NAME	{ raise (Not_implemented "PNAME operations") }
	| PNAME COLON pfld	{ raise (Not_implemented "PNAME operations") }
    ;


opt_prime:          { false }
    | PRIME         { true }


varref_or_prime: varref opt_prime {
        if $2
        then find_or_declare_next $1
        else begin
            let v = $1 in
            v#add_flag HReadOnce;
            v
        end
    }


/* FORSYTE extension */
track_ap: /* empty */	{ HNone }
    | HIDDEN		{ HHide }
    | SHOW			{ HShow }
    ;

/* FORSYTE extension */
prop_decl:
    track_ap ATOMIC NAME ASGN atomic_prop {
        let v = new_var($3) in
        v#add_flag $1;
        (type_tab ())#set_type v (new data_type SpinTypes.TPROPOSITION);
        (spec_scope ())#add_symb v#get_name (v :> symb);
        MDeclProp (fresh_id (), v, $5)
    }
    ;

/* FORSYTE extension */
atomic_prop:
      ALL LPAREN prop_expr RPAREN { PropAll ($3)  }
    | SOME LPAREN prop_expr RPAREN { PropSome ($3) }
    | LPAREN prop_expr RPAREN { PropGlob ($2) }
    | LPAREN atomic_prop PAND atomic_prop RPAREN { PropAnd($2, $4) }
    | LPAREN atomic_prop POR atomic_prop RPAREN { PropOr($2, $4) }
    ;

Opt_priority:	/* none */	{}
	| PRIORITY CONST	{}
	;

full_expr:	expr		{ $1 }
	| Expr		{ $1 }
	;

	/* an Expr cannot be negated - to protect Probe expressions */
Expr	: Probe			{raise (Not_implemented "Probe") }
	| LPAREN Expr RPAREN		{ $2 }
	| Expr AND Expr		{ BinEx(AND, $1, $3) }
	| Expr AND expr		{ BinEx(AND, $1, $3) }
	| expr AND Expr		{ BinEx(AND, $1, $3) }
	| Expr OR  Expr		{ BinEx(OR, $1, $3) }
	| Expr OR  expr		{ BinEx(OR, $1, $3) }
	| expr OR  Expr		{ BinEx(OR, $1, $3) }
	;

Probe	: FULL LPAREN varref RPAREN	{}
	| NFULL LPAREN varref RPAREN	{}
	| EMPTY LPAREN varref RPAREN	{}
	| NEMPTY LPAREN varref RPAREN	{}
	;

Opt_enabler:	/* none */	{}
	| PROVIDED LPAREN full_expr RPAREN	{ }
	| PROVIDED error	{}
	;

basetype: TYPE			{}
	| UNAME			    {}
    | error		        {}	/* e.g., unsigned ':' const */
	;

typ_list: basetype		{}
	| basetype COMMA typ_list	{}
	;

args    : /* empty */		{}
	| arg			{}
	;

prargs  : /* empty */		{ [] }
	| COMMA arg		{ $2 }
	;

margs   : arg			        {}
	| expr LPAREN arg RPAREN	{}
	;

arg : expr	{ [$1] }
    | expr COMMA arg { $1 :: $3 }
	;

rarg	: varref		{ }
	| EVAL LPAREN expr RPAREN	{ }
	| CONST 		{ }
	| MINUS CONST %prec UMIN	{ }
	;

rargs	: rarg			{ }
	| rarg COMMA rargs	{ }
	| rarg LPAREN rargs RPAREN	{ }
	| LPAREN rargs RPAREN		{}
	;

nlst	: NAME			{ }
	| nlst NAME 		{ }
	| nlst COMMA		{ }
	;
%%

