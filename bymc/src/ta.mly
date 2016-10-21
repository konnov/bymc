/*
 * A lexer for threshold automata (see CONCUR'14, CAV'15 papers).
 * This is a temporary language that will most likely be replaced by
 * something more appropriate in the future.
 *
 * We need this parser to encode simple Paxos, which otherwise
 * explodes when encoding in Promela.
 *
 * Igor Konnov, 2015
 */

%{

open Printf
open Lexing

open TaIr

let error message =
    raise (TaErr.SyntaxErr message)

(*
   Check that all locations have have an associated list of integers that
   contains exactly the number of local variables.
 *)
let check_locations decls locs =
    let rec count_locals n = function
        | (Local _) :: tl -> (count_locals (n + 1) tl)
        | _ :: tl -> count_locals n tl
        | [] -> n
    in
    let nlocals = count_locals 0 decls in
    let check_one (loc_name, vals) =
        let nvals = List.length vals in
        if nlocals <> nvals
        then let m =
            sprintf "All locations must contain the list of %d integer values, found %d in %s" nlocals nvals loc_name in
            raise (TaErr.SemanticErr m)
    in
    List.iter check_one locs


let loc_tbl = ref (Hashtbl.create 10)

let reset_locs () =
    Hashtbl.clear !loc_tbl

let put_loc name =
    let j = Hashtbl.length !loc_tbl in
    Hashtbl.add !loc_tbl name j

let find_loc name =
    try Hashtbl.find !loc_tbl name
    with Not_found ->
        raise (TaErr.SemanticErr (sprintf "location %s not found" name))

%}

%token  SKEL PARAMETERS
%token	SEMI
%token	WHEN DO
%token	LOCAL SHARED
%token	<int> CONST
%token	<string> NAME

%token  INITS ASSUME LOCATIONS RULES SPECIFICATIONS
%token  LTLF LTLG
%token  IMPLIES
%token  OR AND
%token  NE EQ LT GT LE GE
%token  NOT
%token  PLUS MINUS
%token  MULT
%token  COLON COMMA LPAREN RPAREN LBRACE RBRACE LCURLY RCURLY
%token  PRIME
%token  EOF

%start  start
%type   <TaIr.Ta.ta_t> start

%%

start
    : SKEL n = NAME LCURLY
        ds = decls
        ass = assumptions
        locs = locations
        is = inits
        rs = rules
        specs = specifications
      RCURLY EOF
        {
            check_locations ds locs;
            TaIr.mk_ta n (List.rev ds) ass locs is rs specs
        }
    (* error handling *)
    | SKEL NAME LCURLY decls assumptions locations inits rules specifications error
        { error "expected: '}' after specifications {..}" }
    | SKEL NAME LCURLY decls assumptions locations inits rules error
        { error "expected: specifications after rules {..}" }
    | SKEL NAME LCURLY decls assumptions locations inits error
        { error "expected: rules {..} after inits {..}" }
    | SKEL NAME LCURLY decls assumptions locations error
        { error "expected: inits {..} after locations {..}" }
    | SKEL NAME LCURLY decls assumptions error
        { error "expected: locations {..} after assumptions {..}" }
    | SKEL NAME LCURLY decls error
        { error "expected: assumptions {..} after declarations" }
	;

decls
    :                           { reset_locs (); [] }
    | tl = decls ds = decl      { ds @ tl }
    ;

decl
    : LOCAL ls = locals SEMI        { ls }
    | SHARED sh = shared SEMI       { sh }
    | PARAMETERS ps = params SEMI   { ps }
    ;

locals
    : n = NAME
        { [ (Local n) ] }

    | ns = locals COMMA n = NAME
        { (Local n) :: ns }
    ;

shared
    : n = NAME
        { [ (Shared n) ] }

    | ns = shared COMMA n = NAME
        { (Shared n) :: ns }
    ;

params
    : n = NAME
        { [ (Param n) ] }

    | ns = params COMMA n = NAME
        { (Param n) :: ns }
    ;

assumptions
    : ASSUME LPAREN CONST RPAREN LCURLY es = rel_expr_list RCURLY
        { es }
    ;

inits
    : INITS LPAREN CONST RPAREN LCURLY es = rel_expr_list RCURLY
        { es }
    ;

rules
    : RULES LPAREN CONST RPAREN LCURLY rs = rule_list RCURLY
        { rs }
    ;

rule_list
    : { [] }

    | CONST COLON src = NAME IMPLIES dst = NAME
        WHEN g = bool_expr
        DO LCURLY a = bool_expr RCURLY SEMI rs = rule_list
        {
            let r = TaIr.mk_rule (find_loc src) (find_loc dst) g a in
            r :: rs
        } 
    
    | error { error "expected '<num>: <loc> -> <loc> when (..) do {..}" }
    ;


rel_expr_list
    : { [] }

    | e = rel_expr SEMI es = rel_expr_list
        { e :: es }
    ;

locations
    : LOCATIONS LPAREN CONST RPAREN LCURLY ls = locs RCURLY
        { ls }
    ;

locs
    : { [] }
    | l = one_loc SEMI ls = locs
        { l :: ls }
    ;

one_loc
    : n = NAME COLON LBRACE l = int_list RBRACE
        { put_loc n; (n, l) }
    | error { error "expected '<name>: [ int(; int)* ]'" }
    ;

int_list
    : i = CONST { [i] }
    | i = CONST SEMI { [i] }
    | i = CONST SEMI is = int_list
        { i :: is }
    ;

bool_expr
    : e = and_expr
        { e }

    | l = and_expr OR r = bool_expr
        { Or (l, r) }

    | error { error "expected a boolean expression" }
    ;

and_expr
    : e = not_expr
        { e }

    | l = not_expr AND r = and_expr
        { And (l, r) }
    ;

not_expr
    : e = cmp_expr      { Cmp e }
    | NOT e = not_expr  { Not e }
    | LPAREN e = bool_expr RPAREN { e }
    ;

(* we need this to deal with parentheses *)
rel_expr
    : e = cmp_expr
        { e }

    | LPAREN e = rel_expr RPAREN
        { e }
    ;

cmp_expr
    : l = arith_expr GT r = arith_expr  { Gt (l, r) }
    | l = arith_expr GE r = arith_expr  { Geq (l, r) }
    | l = arith_expr LT r = arith_expr  { Lt (l, r) }
    | l = arith_expr LE r = arith_expr  { Leq (l, r) }
    | l = arith_expr EQ r = arith_expr  { Eq (l, r) }
    | l = arith_expr NE r = arith_expr  { Neq (l, r) }
    ;

arith_expr
    : e = mul_expr                      { e }
    | LPAREN e = arith_expr RPAREN      { e }
    | i = mul_expr PLUS j = mul_expr    { Add (i, j) }
    | i = mul_expr MINUS j = mul_expr   { Sub (i, j) }
    ;

mul_expr
    : i = int_expr                      { i }
    | i = int_expr MULT j = int_expr    { Mul (i, j) }
    ;

int_expr
    : i = CONST                     { Int i }
    | n = NAME                      { Var n }
    | n = NAME PRIME                { NextVar n }
    ;


specifications
    : SPECIFICATIONS LPAREN CONST RPAREN LCURLY forms = form_list RCURLY
    { forms } 

form_list
    : { Accums.StrMap.empty }

    | n = NAME COLON f = ltl_expr SEMI fs = form_list
        { Accums.StrMap.add n f fs }
    ;

ltl_expr
    : e = ltl_or_expr { e }
    | l = ltl_or_expr IMPLIES r = ltl_expr
        { LtlImplies (l, r) }
    ;

ltl_or_expr
    : e = ltl_and_expr
        { e }

    | l = ltl_and_expr OR r = ltl_or_expr
        { LtlOr (l, r) }

    | error { error "expected a boolean expression" }
    ;

ltl_and_expr
    : e = ltl_modality_expr
        { e }

    | l = ltl_modality_expr AND r = ltl_and_expr
        { LtlAnd (l, r) }
    ;

ltl_modality_expr
    : LTLF f = ltl_modality_expr { LtlF f}
    | LTLG f = ltl_modality_expr { LtlG f}
    | e = ltl_not_expr { e }
    ;


ltl_not_expr
    : e = cmp_expr      { LtlCmp e }
    | NOT e = ltl_not_expr  { LtlNot e }
    | LPAREN e = ltl_expr RPAREN { e }
    ;

