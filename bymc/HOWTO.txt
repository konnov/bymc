0. WHAT IS THAT?

ByMC is a tool for model checking fault-tolerant distributed algorithms.
More details to be found at: http://forsyte.at/software/bymc/

1. PREREQUISITES

 * ocaml and ocamlbuild (not earlier than 3.11.0)
 * ocamlgraph: http://ocamlgraph.lri.fr/
 * yices 1.x: http://yices.csl.sri.com/download.shtml
 * spin: http://spinroot.com/spin/Man/README.html#S2
 * gcc
 * python

2. COMPILING

# building (you need ocaml and ocamlbuild)
cd bymc # (the directory with this README)
./make.sh

3. EXAMPLES

You can find the examples at the tool's website:

http://forsyte.at/software/bymc/#examples

4. RUNNING

# checking models with concrete parameters using spin
./run-concrete 'N=3,T=1,F=1' ${spin13-benchmarks}/cond-consensus.pml termination

# parameterized model checking with the abstraction-refinement

./cegar ${fmcad13-benchmarks}/bcast-byz.pml relay

(you can invoke cegar from any directory you want)

# follow the messages by the script...

# if you want to provide an invariant, then introduce one like tx_inv
# in bcast_symb.
# The tool will check automatically if it is an invariant.
#
# after that run cegar once more:
./cegar ${fmcad13-benchmarks}/bcast-byz.pml relay

# the manual execution of the tool chain (most likely, you don't need it!)

OCAMLRUNPARAM=b ./bymc.native -a bcast-byz.pml
view original.prm     # the original system as parsed by the tool
view abs-interval.prm # the interval abstraction
view abs-counter-general.prm  # the counter abstraction
view abs-vass.prm     # the VASS representation used for refinement
spin -a -N unforg.never abs-counter.prm
gcc -o pan pan.c && ./pan -a -m1000000
# see a counter example produced in Spin
spin -t -N unforg.never abs-counter.prm | grep '{' >spin.trace
view trace.ys         # the trace encoded in yices (SMT solver)

# properties we usually check:
{unforg,corr,relay}

# see a counter example in VASS and (perhaps) refine the system:

OCAMLRUNPARAM=b ./bymc.native -t spin.trace bcast-byz.pml

5. MISC

Should you have any questions, ask Igor Konnov <konnov@forsyte.at>

