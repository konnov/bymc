# ".ta": a format of threshold automata

Igor Konnov, May 2019

In [CONCUR14](http://forsyte.at/wp-content/uploads/concur14-reachability.pdf), we have introduced threshold automata as part of a theoretical framework for encoding threshold-guarded fault-tolerant distributed algorithms. In ByMC, we have introduced an intermediate language for threshold automata, which was not designed to be human-readable. However, later, we started to use this language to encode threshold automata directly, without involving additional abstractions. Hence, we added a few language constructs that ease specifying threshold automata by humans. The [threshold automata](https://link.springer.com/article/10.1007%2Fs10703-017-0297-4) in ByMC should adhere the following grammar in [EBNF](https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form).

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
(* locations: a location name can be used a counter in an LTL formula *)
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
(* inside ltl_expr, cmp_expr can refer to the following varibles and parameters:
   locations, local variables, shared variables, parameters, and unknowns *)
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

1. While originally threshold automata had only variables and constants declared with the qualifiers `shared`, `local`, and `parameters`, we have added `unknowns` to express the coefficients to be synthesized in the paper at [OPODIS17](http://drops.dagstuhl.de/opus/volltexte/2018/8635/). Hence, `unknowns` should be only used for the synthesis problems, not verification. See the examples in the [OPODIS benchmarks](https://github.com/konnov/fault-tolerant-benchmarks/tree/master/opodis17/ta).

1. The format does not restrict the Boolean structure of the LTL formulas. However, different techniques impose different constraints on the formula structure. For instance, the technique from [POPL17](http://forsyte.at/wp-content/uploads/popl17main-main116-p-9d29769-29971-final.pdf) restricts the Boolean structure of counter comparisons, see the paper for details. Whereas [FMSD17](https://link.springer.com/article/10.1007/s10703-017-0297-4) requires LTL formulas to have the shape `[]f`, where `f` is an arbitrary Boolean formula following the syntax of `bool_expr`. See the examples in [ISOLA benchmarks](https://github.com/konnov/fault-tolerant-benchmarks/tree/master/isola18/ta).

1. The ta-syntax is quite low-level, which results in a lot of duplication. To avoid that, one can use a macro-preprocessor such as [mako templates](https://www.makotemplates.org/). See [random19 benchmarks](https://github.com/konnov/fault-tolerant-benchmarks/tree/master/random19) for an example.







