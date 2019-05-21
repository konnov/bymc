# The format of threshold automata

The [threshold automata](https://link.springer.com/article/10.1007%2Fs10703-017-0297-4) in ByMC should adhere the following grammar in [EBNF](https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form).

```ebnf
ta ::= ("thresholdAutomaton" | "skel") id "{" decls defines assumptions locations inits rules specs "}"
(* declarations of variables, parameters, and unknowns *)
decls ::= { declaration }
declaration ::= ("local" ids | "shared" ids | "parameters" ids | "unknowns" ids) ";"
(* simple macros to avoid repetition *)
defines ::= { define }
define ::= "define" macro_name = arith_expr ";"
macro_name ::= <a sequence of capital Latin letters, digits, and "_", starting with a letter or "_">
(* assumptions about the relation between the parameters and unknowns *)
assumptions ::= "assume" "(" size ")" "{" bool_exprs "}"
(* locations of a threshold automaton; each location assigns values to the local variables *)
locations ::= "locations" "(" size ")" "{" {loc} "}"
loc ::= id ":" "[" nat { ";" nat } "]" ";"
(* constraints on the initial states *)
inits ::= "inits" "(" size ")" "{" rel_exprs "}"
(* automata rules *)
rules ::= "rules" "(" seq_no ")" "{" {rule} "}"
rule  ::= seq_no ":" id "->" id "when" "(" guard ")" "do" "{" {action} "}" ";"
(* a guard is either true, which is expressed with 1, or a Boolean expression *)
guard ::= "1" | bool_expr
(* an action is either an assignment, or a statement that some variables are not changing *)
acts ::= (* empty *) | act { act }
act  ::= id "'" "=" arith_expr ";"
(* specifications *)
specs ::= "specifications" "(" size ")" "{" forms "}"
forms ::= (* empty *) | id ":" ltl_expr ";" { forms }
ltl_expr ::= cmp_expr | "!" ltl_expr | "<>" ltl_expr | "[]" ltl_expr
		  | ltl_expr "->" ltl_expr | ltl_expr "||" ltl_expr | ltl_expr "&&" ltl_expr
		  | "(" ltl_expr ")"
(* expressions *)
bool_exprs ::= (* empty *) | bool_expr ";" { bool_exprs }
bool_expr  ::= "true" | cmp_expr | "(" bool_expr ")"
		     | "!" bool_expr | bool_expr "||" bool_expr | bool_expr "&&" bool_expr
cmp_expr   ::= arith_expr ">" arith_expr | arith_expr ">=" arith_expr | arith_expr "<" arith_expr
		     | arith_expr "<=" arith_expr | arith_expr "==" arith_expr | arith_expr "!=" arith_expr
rel_exprs  ::= (* empty *) | rel_expr ";" { rel_exprs }
rel_expr   ::= cmp_expr | "(" rel_expr ")"
arith_expr ::= nat | id | id "'" | macro_name | "(" arith_expr ")"
			| arith_expr "+" arith_expr | arith_expr "-" arith_expr
			| arith_expr "*" arith_expr | "-" arith_expr 
(* sequence numbers are introduced by the generated code, they can be replaced by 0 *)
seq_no ::= nat
(* list sizes are introduced by the generated code, they can be replaced by 0 *)
size ::= nat
(* the standard definitions *)
nat ::= <a sequence of digits>
ids ::= id { ", " id }
id ::= <a sequence of Latin letters, digits, and "_", starting with a letter or "_", having at least one small letter>
```

## Comments

While originally threshold automata had only variables and constants declared with the qualifiers `shared`, `local`, and `parameters`, we have added `unknowns` to express the coefficients to be synthesized in the paper at [OPODIS'17](http://drops.dagstuhl.de/opus/volltexte/2018/8635/). Hence, `unknowns` should be only used for the synthesis problems, not verification.
