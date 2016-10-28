
0. WHAT IS THAT?

ByMC is a tool for model checking fault-tolerant distributed algorithms.
More details to be found at: http://forsyte.at/software/bymc/

Should you have any questions, ask Igor Konnov <konnov at forsyte.at>


CONTENTS

1. PREREQUISITES
2. COMPILING
3. EXAMPLES
4. RUNNING
5. HOW TO INSTALL OCAML AND THE LIBRARIES?
6. INSTALLING PYCUDD
7. MISC


1. PREREQUISITES

 * python 2.x
 * ocaml and ocamlbuild (not earlier than 3.11.0)
 * ocaml batteries: http://batteries.forge.ocamlcore.org/
 * ocamlgraph: http://ocamlgraph.lri.fr/
 * ocamlunit (OPTIONAL: if you want to run unit tests)
 * sexplib
 * ctypes and ctypes-foreign (OPTIONAL: when you compile with mathsat)
 * at least one SMT solver:
    * yices 1.x: http://yices.csl.sri.com/download.shtml
    * Microsoft Z3
    * Any decent SMT solver that supports SMTLIB2, logic QF_ALIA,
      model generation, and unsat cores.
 * one of the model checkers (OPTIONAL: when not using verifypa-post):
     - spin: http://spinroot.com/spin/Man/README.html#S2
     - nusmv: http://nusmv.fbk.eu/NuSMV/download/getting-v2.html
     - faster: http://www.lsv.ens-cachan.fr/Software/fast/
 * gcc (OPTIONAL: if you are going to use spin)
 * lingeling: http://fmv.jku.at/lingeling/
     (OPTIONAL: if you want to run bounded model checking with nusmv + lingeling)
 * pycudd (OPTIONAL and DEPRECATED:
     see Sec. 6, if you want to reproduce the results on the diameter, or to
     check the algorithms with FASTer, as in the paper at CONCUR'14)

If you do not know how to install ocaml and ocaml libraries in your system,
check with "HOW TO INSTALL OCAML AND THE LIBRARIES?"

2. COMPILING

# building (you need ocaml and ocamlbuild)
cd bymc # (the directory with this README)
make

3. EXAMPLES

You can find the examples at the tool's website:

http://forsyte.at/software/bymc/#examples

4. RUNNING

4.1 PARTIAL ORDERS AND ACCELERATION IN SMT (our CAV'15 and POPL'17 papers)

using Z3:

./verifypa-post ${benchmarks}/2015/promela/bcast-byz.pml unforg --smt 'lib2|z3|-in|-smt2'

or another SMT solver:

./verifypa-post ${benchmarks}/2015/promela/bcast-byz.pml unforg --smt 'lib2|mysolver|arg1|arg2|arg3'

4.2. SPIN

# checking models with concrete parameters using spin
./verifyco-spin 'N=3,T=1,F=1' ${spin13-benchmarks}/cond-consensus.pml termination

Parameterized model checking with the abstraction-refinement:

./verifypa-spin ${benchmarks}/bcast-byz.pml relay

(you can invoke verifypa-* scripts from any directory you want)

# follow the messages by the script...

# if you want to provide an invariant, then introduce one like tx_inv
# in bcast_symb.
# The tool will check automatically, whether it is an invariant.
#
# after that run cegar once more:
./verifypa-spin ${benchmarks}/bcast-byz.pml relay


4.3. NuSMV with BDDs

Parameterized model checking with the abstraction-refinement:

./verifypa-nusmv-bdd ${benchmarks}/bcast-byz.pml relay


4.4. NuSMV with BMC

Parameterized model checking with the abstraction-refinement:

./verifypa-nusmv-bmc -k length ${benchmarks}/bcast-byz.pml relay

or using lingeling for <length2> steps
    (refinement only up to <length> steps is supported):

./verifypa-nusmv-bmc -k length --lingeling length2 \
    ${benchmarks}/bcast-byz.pml relay

or using lingeling for <length2> steps
    (refinement only up to <length> steps is supported):

./verifypa-nusmv-bmc -k length --lingeling length2 \
    --plingeling num_workers \
    ${benchmarks}/bcast-byz.pml relay


4.5 FAST

./verifypa-fast --plugin <fast-plugin> ${benchmarks}/bcast-byz.pml unforg


4.6 COMPUTING DIAMETER (of PIA data abstraction)

./analyse ${benchmarks}/bcast-byz.pml bounds

gives bounds on the diameter of counter systems and counter abstractions

the new way to do that is (our CAV'15 submission):

./verifypa-post ${benchmarks}/bcast-byz.pml all

The latter will check the properties as well (Sec. 4.6).


5. HOW TO INSTALL OCAML AND THE LIBRARIES?

5.1 Your package manager

The easiest way to install the dependencies is to use your package manager,
i.e., apt-get, zypper, etc. For instance, this tool is periodically built
on Debian Wheezy, which makes all the libraries available via its package
manager apt-get.

5.1 Ocamlbrew

If you do not have ocaml and the required ocaml packages, consider using
ocamlbrew: http://opam.ocaml.org/doc/Quick_Install.html#h4-Usingocamlbrew

In case you experience problems with installation of Oasis, which we do not
use, install ocamlbrew as follows:

$ curl -kL https://raw.github.com/hcarty/ocamlbrew/master/ocamlbrew-install \
    | env OCAMLBREW_FLAGS="-r -b $HOME/ocamlbrew" bash

Ocamlbrew bootstraps the whole ocaml infrastructure together with the package
manager called opam. As soon as opam is in place, you can install the
packages as follows:

$ opam install batteries ounit ocamlgraph sexplib

If you want to compile mathsat's library, you have to also install:

$ opam install ctypes ctypes-foreign

(Do not forget to include the line
'source ~/ocamlbrew/ocaml-4.00.1/etc/ocamlbrew.bashrc'
in your ~/.bashrc or ~/.zshrc before doing that)

6. INSTALLING PYCUDD (DEPRECATED)

WARNING: PyCUDD is required only for the script ./analyse that computes
reachability bounds as in the paper accepted at CONCUR'14. This script
is superseded by ./verify-post that neither uses pycydd, nor nusmv.

PyCUDD is required when ./analysis is run with the property 'bounds'.
To compile pycudd:
  $ cd ../deps/pycudd2.0.2/cudd-2.4.2
  $ make # uncomment XCFLAGS for x86_64 in Makefile if needed
  $ mkdir lib
  $ make libso
  $ cd ../pycudd
  $ make


7. MISC

Nothing here yet

