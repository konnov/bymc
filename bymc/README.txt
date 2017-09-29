
0. WHAT IS THAT?
================

ByMC is a tool for model checking (and synthesis) of fault-tolerant distributed
algorithms.  More details to be found at: http://forsyte.at/software/bymc/

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
================

 * python 2.x
 * ocaml and ocamlbuild (not earlier than 3.11.0)
 * ocaml batteries: http://batteries.forge.ocamlcore.org/
 * ocamlgraph: http://ocamlgraph.lri.fr/
 * ocamlunit (OPTIONAL: if you want to run unit tests)
 * ocamlmpi (github), libopenmpi-dev (linux) and openmpi-bin (linux)
    (if you want to do verification or synthesis in parallel)
    (if needed, use: $ sudo ln -s /etc/alternatives/mpi /usr/include/mpi/)
 * sexplib
 * ctypes and ctypes-foreign (OPTIONAL: when you compile with mathsat)
 * at least one SMT solver:
    * Microsoft Z3 (ocaml bindings)
    * yices 1.x: http://yices.csl.sri.com/download.shtml
    * Any decent SMT solver that supports SMTLIB2, logic QF_ALIA,
      model generation, and unsat cores.

 * one of the model checkers (OPTIONAL: when not using verifypa-schema):
     - spin: http://spinroot.com/spin/Man/README.html#S2
     - nusmv: http://nusmv.fbk.eu/NuSMV/download/getting-v2.html
     - faster: http://www.lsv.ens-cachan.fr/Software/fast/

 * gcc (OPTIONAL: if you are going to use spin)

 * lingeling: http://fmv.jku.at/lingeling/
     (OPTIONAL: if you want to run bounded model checking with nusmv + lingeling)

 * pycudd (OPTIONAL and DEPRECATED:
     see Sec. 6, if you want to reproduce the results on the diameter, or to
     check the algorithms with FASTer, as in the paper at CONCUR'14. Better
     download ByMC 0.6.7)

If you do not know how to install ocaml and ocaml libraries in your system,
check with "HOW TO INSTALL OCAML AND THE LIBRARIES?"


2. COMPILING
============

# building (you need ocaml and ocamlbuild)
cd bymc # (the directory with this README)
make


3. EXAMPLES
===========

You can find the examples at the tool's website:

  [http://forsyte.at/software/bymc/]

as well as in the following github repository:

  [https://github.com/konnov/fault-tolerant-benchmarks]


4. RUNNING
==========

4.1 PARTIAL ORDERS AND ACCELERATION IN SMT (CAV'15, POPL'17, FMSD'17)
---------------------------------------------------------------------

using Z3 and OCaml bindings:

$ ./verifypa-schema ${benchmarks}/popl17/promela/bcast-byz.pml unforg

or an SMT solver that supports SMTLIB2:

$ ./verifypa-post ${benchmarks}/popl17/promela/bcast-byz.pml unforg --smt 'lib2|mysolver|arg1|arg2|arg3'


4.2 SYNTHESIS (submission to OPODIS'17)

using Z3 and OCaml bindings (single core):

$ ./syntpa-schema test/bcast-byz-ta-synt.ta all

or running the parallel version with MPI (set $PROCS to the number of MPI processes):

$ mpirun -n $PROCS --output-filename out \
  ./syntpa-schema test/bcast-byz-ta-synt.ta all -O schema.tech=ltl-mpi


You can also enumerate all possible solutions by adding -O synt.all=1:

$ ./syntpa-schema test/bcast-byz-ta-synt.ta all -O synt.all=1


4.3. SPIN (our FMCAD'13 paper)
------------------------------

# checking models with concrete parameters using spin
$ ./verifyco-spin 'N=3,T=1,F=1' ${spin13-benchmarks}/cond-consensus.pml termination

Parameterized model checking with the abstraction-refinement:

$ ./verifypa-spin ${benchmarks}/bcast-byz.pml relay

(you can invoke verifypa-* scripts from any directory you want)

# follow the messages by the script...

# if you want to provide an invariant, then introduce one like tx_inv
# in bcast_symb.
# The tool will check automatically, whether it is an invariant.
#
# after that run cegar once more:
$ ./verifypa-spin ${benchmarks}/bcast-byz.pml relay


4.4. NuSMV with BDDs (like in FMCAD'13 but symbolic)
----------------------------------------------------

Parameterized model checking with the abstraction-refinement:

$ ./verifypa-nusmv-bdd ${benchmarks}/bcast-byz.pml relay


4.5. NuSMV with BMC (like in CONCUR'14)
---------------------------------------

Parameterized model checking with the abstraction-refinement:

$ ./verifypa-nusmv-bmc -k length ${benchmarks}/bcast-byz.pml relay

or using lingeling for <length2> steps
    (refinement only up to <length> steps is supported):

$ ./verifypa-nusmv-bmc -k length --lingeling length2 \
    ${benchmarks}/bcast-byz.pml relay

or using lingeling for <length2> steps
    (refinement only up to <length> steps is supported):

$ ./verifypa-nusmv-bmc -k length --lingeling length2 \
    --plingeling num_workers \
    ${benchmarks}/bcast-byz.pml relay


4.6 FAST (as reported in CONCUR'14)
-----------------------------------

$ ./verifypa-fast --plugin <fast-plugin> ${benchmarks}/bcast-byz.pml unforg


4.7 COMPUTING DIAMETER (of PIA data abstraction, as in CONCUR'14)
--------------------------------------------------------------------------

$ ./analyse ${benchmarks}/bcast-byz.pml bounds

gives bounds on the diameter of counter systems and counter abstractions

the new way to do that is (our CAV'15 submission):

$ ./verifypa-post ${benchmarks}/bcast-byz.pml all

The latter will check the properties as well (Sec. 4.6).


5. HOW TO INSTALL OCAML AND REQUIRED LIBRARIES?
===============================================

5.1. Ocamlbrew
-------------

If you do not have ocaml and the required ocaml packages, consider using
ocamlbrew: http://opam.ocaml.org/doc/Quick_Install.html#h4-Usingocamlbrew

In case you experience problems with installation of Oasis, which we do not
use, install ocamlbrew as follows:

$ curl -kL https://raw.github.com/hcarty/ocamlbrew/master/ocamlbrew-install \
    | env OCAMLBREW_FLAGS="-r -b $HOME/ocamlbrew" bash

Ocamlbrew bootstraps the whole ocaml infrastructure together with the package
manager called opam. As soon as opam is in place, you can install the
packages as follows:

$ opam install batteries ounit ocamlgraph sexplib menhir lazy-trie

(Do not forget to include the line
'source ~/ocamlbrew/ocaml-4.XX.X/etc/ocamlbrew.bashrc'
in your ~/.bashrc or ~/.zshrc before doing that)

If you want to compile mathsat's library, you have to also install:

$ opam install ctypes ctypes-foreign

5.2. Installing ocamlmpi
------------------------

As of September 2017, MPI bindings for ocaml are not available in opam.
To install ocamlmpi, do the following:
  
  1. Download the latest version from: https://github.com/xavierleroy/ocamlmpi
  2. edit Makefile and change MPIINCDIR, if needed
  2. make && make opt && make install
  

6. INSTALLING PYCUDD (DEPRECATED)
=================================

WARNING: PyCUDD is required only for the script ./analyse that computes
reachability bounds as in the paper accepted at CONCUR'14. This script
is superseded by ./verify-schema that neither uses pycydd, nor nusmv.

PyCUDD is required when ./analysis is run with the property 'bounds'.
To compile pycudd:
  $ cd ../deps/pycudd2.0.2/cudd-2.4.2
  $ make # uncomment XCFLAGS for x86_64 in Makefile if needed
  $ mkdir lib
  $ make libso
  $ cd ../pycudd
  $ make


7. MISC
=======

Nothing here yet

