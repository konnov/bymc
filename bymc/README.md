
# 0. WHAT IS THAT?

ByMC is a tool for parameterized model checking (and synthesis) of fault-tolerant distributed
algorithms.  More details to be found at: [ByMC](http://forsyte.at/software/bymc/)

Should you have questions, ask Igor Konnov `<konnov at forsyte.at>`


## CONTENTS

 1. PREREQUISITES
 2. COMPILING
 3. EXAMPLES
 4. RUNNING
 5. HOW TO INSTALL OCAML AND THE PREREQUISITES?
 6. INSTALLING PYCUDD
 7. PUBLICATIONS


# 1. PREREQUISITES

 * `python` 2.x
 * `ocaml` and `ocamlbuild` (up to 4.06.1)
 * [`ocaml batteries`](http://batteries.forge.ocamlcore.org/)
 * [`ocamlgraph`](http://ocamlgraph.lri.fr/)
 * `ocamlunit` (__OPTIONAL__: if you want to run unit tests)
 * [`ocamlmpi`](https://github.com/xavierleroy/ocamlmpi), libopenmpi-dev (linux) and openmpi-bin (linux),
    if you want to do verification or synthesis in parallel
 * `sexplib`
 * at least one SMT solver:
    * Microsoft `z3` and its ocaml bindings
    * Any decent SMT solver that supports `SMTLIB2`, logic `QF_LIA`,
      model generation, and unsat cores.
    * [`yices` 1.x](http://yices.csl.sri.com/download.shtml) (__DEPRECATED__)

 * one of the model checkers (__OPTIONAL__: when not using verifypa-schema):
     - [`spin`](http://spinroot.com/spin/Man/README.html#S2)
     - [`nusmv`](http://nusmv.fbk.eu/NuSMV/download/getting-v2.html)
     - [`faster`](http://www.lsv.ens-cachan.fr/Software/fast/)

 * `gcc` (__OPTIONAL__: if you are going to use spin)
 * `ctypes` and `ctypes-foreign` (__OPTIONAL__: to compile against mathsat)
 * [`lingeling`](http://fmv.jku.at/lingeling/)
     (__OPTIONAL__: if you want to run bounded model checking with nusmv + lingeling)

If you do not know how to install ocaml and ocaml libraries in your system,
check with "HOW TO INSTALL OCAML AND THE LIBRARIES?"


# 2. COMPILING

Run the `make` in the directory that contains this README file:

```bash
$ make
```


# 3. EXAMPLES

You can find the examples at the [ByMC website]([http://forsyte.at/software/bymc/])

as well as at our [benchmarks repository](https://github.com/konnov/fault-tolerant-benchmarks)

# 4. RUNNING

## 4.1 PARTIAL ORDERS AND ACCELERATION IN SMT

This technique is explained in [CAV15], [POPL17], [FMSD17]

Using Z3 and OCaml bindings:

```bash
$ ./verifypa-schema ${benchmarks}/popl17/promela/bcast-byz.pml unforg
```

or an SMT solver that supports SMTLIB2:

```bash
$ ./verifypa-schema ${benchmarks}/popl17/promela/bcast-byz.pml unforg --smt 'lib2|mysolver|arg1|arg2|arg3'
```


## 4.2 SYNTHESIS

This technique is explained in [OPODIS17].

Using Z3 and OCaml bindings (single core):

```bash
$ ./syntpa-schema test/bcast-byz-ta-synt.ta all
```

or running the parallel version with MPI (set `$PROCS` to the number of MPI processes):

```bash
$ mpirun -n $PROCS --output-filename out ./syntpa-schema test/bcast-byz-ta-synt.ta all -O schema.tech=ltl-mpi
```


You can also enumerate all possible solutions by adding `-O synt.all=1`:

```bash
$ ./syntpa-schema test/bcast-byz-ta-synt.ta all -O synt.all=1
```


## 4.3. SPIN

This technique is explained in [FMCAD13].

Checking models with concrete parameters using spin:

```bash
$ ./verifyco-spin 'N=3,T=1,F=1' ${spin13-benchmarks}/cond-consensus.pml termination
```

Parameterized model checking with the abstraction-refinement:

```bash
$ ./verifypa-spin ${benchmarks}/bcast-byz.pml relay
```

You can invoke `verifypa-*` scripts from any directory you want.

Follow the messages by the script. If you want to provide an invariant,
then introduce one like `tx_inv` in `bcast_symb`.
The tool will check automatically, whether it is an invariant.

After that run the tool again:

```bash
$ ./verifypa-spin ${benchmarks}/bcast-byz.pml relay
```


## 4.4. NuSMV with BDDs

Data and counter abstraction like in [FMCAD13] but using binary decision
diagrams. The experiments were reported in [INFCOMP17] and [CONCUR14].

Parameterized model checking with the abstraction-refinement:

```bash
$ ./verifypa-nusmv-bdd ${benchmarks}/bcast-byz.pml relay
```


## 4.5. NuSMV with BMC

Data and counter abstraction like in [FCMAD13] but using bounded model checking
that is implemented in `NuSMV`. The experiments were reported in
[INFCOMP17] and [CONCUR14].

```bash
$ ./verifypa-nusmv-bmc -k length ${benchmarks}/bcast-byz.pml relay
```

or using lingeling for `<length2>` steps
    (refinement only up to `<length>` steps is supported):

```bash
$ ./verifypa-nusmv-bmc -k length --lingeling length2 ${benchmarks}/bcast-byz.pml relay
```

or using lingeling for `<length2>` steps
    (refinement only up to `<length>` steps is supported):

```bash
$ ./verifypa-nusmv-bmc -k length --lingeling length2 \
    --plingeling num_workers \
    ${benchmarks}/bcast-byz.pml relay
```


## 4.6 FAST

Acceleration of counter automata that is implemented in `faster`. The
experiments were reported in [INFCOMP17] and [CONCUR14].

```bash
$ ./verifypa-fast --plugin <fast-plugin> ${benchmarks}/bcast-byz.pml unforg
```


## 4.7 COMPUTING DIAMETER

The new way to compute the diameter bound:

```bash
$ ./verifypa-schema ${benchmarks}/bcast-byz.pml bounds
```

The old way as was initially implemented for [CONCUR14] is as follows:

```bash
$ ./analyse ${benchmarks}/bcast-byz.pml bounds
```

This technique requires `pycudd`, see Section 6.


# 5. HOW TO INSTALL OCAML AND REQUIRED LIBRARIES?

## 5.1. Ocamlbrew

If you do not have ocaml and the required ocaml packages, consider using
[`ocamlbrew`](http://opam.ocaml.org/doc/Quick_Install.html#h4-Usingocamlbrew)

In case you experience problems with installation of `oasis`, which we do not
use, install `ocamlbrew` as follows:

```bash
$ curl -kL https://raw.github.com/hcarty/ocamlbrew/master/ocamlbrew-install \
    | env OCAMLBREW_FLAGS="-r -b $HOME/ocamlbrew" bash
```

The script `ocamlbrew` bootstraps the whole ocaml infrastructure together with
the package manager called `opam`. As soon as `opam` is in place, you can
install the packages as follows:

```bash
$ opam install batteries ounit ocamlgraph sexplib menhir lazy-trie
```

(Do not forget to include the line
`'source ~/ocamlbrew/ocaml-4.XX.X/etc/ocamlbrew.bashrc'`
in your `~/.bashrc` or `~/.zshrc` before doing that)

If you want to compile the tool against `mathsat`, you have to also install:

```bash
$ opam install ctypes ctypes-foreign
```

## 5.2. Installing ocamlmpi

As of September 2017, MPI bindings for ocaml are not available from `opam`.
To install `ocamlmpi`, do the following:
  
  1. Download the latest version of [ocamlmpi](https://github.com/xavierleroy/ocamlmpi)
  2. Hack the files `opam` and `Makefile` if needed (see below)
  3. Pin the package to the `ocamlmpi` directory:
  
```bash
  opam pin add ocamlmpi . -n
```


  4. Run:
  
```bash
opam install ocamlmpi --verbose
```

__Hack__ for MacOS X: if `conf-mpi` is not working, remove `conf-mpi` from the file
    `opam` and overwrite `MPIINCDIR`, `MPILIBDIR`, `MPICC`, and `MPIRUN` with the path
    pointing to `/usr/local/{include,lib,bin,bin}/openmpi`

__Hack__ for OCaml 4.02.0 and later: edit Makefile, add option `-unsafe-string` to the Makefile variables `OCAMLC`
    and `OCAMLOPT`.
  

## 5.3. Installing z3

Consider installing the z3 package by issuing:

```bash
opam install z3
```

Here are instructions for z3 4.7.1. For other versions, check README in the
distribution of z3:

  1. Download z3 from: https://github.com/Z3Prover/z3/releases

  2. Compile and install z3 by running:

```bash
python scripts/mk_make.py --ml -p ~/usr
cd build; make
make install
```
  
  If you have previous versions of Z3 ocaml bindings, remove them by issuing:

```bash
ocamlfind remove Z3
```

  
# 6. INSTALLING PYCUDD

__WARNING__: PyCUDD is required only by the script `analyse` that computes
reachability bounds as in [CONCUR14]. This script
is superseded by `verify-schema`, which requires neither `pycydd`, nor `nusmv`. Note that option has not been tested for long time.

To compile pycudd, run the following:

```bash
  $ cd ../deps/pycudd2.0.2/cudd-2.4.2
  $ make # uncomment XCFLAGS for x86_64 in Makefile if needed
  $ mkdir lib
  $ make libso
  $ cd ../pycudd
  $ make
```


# 7. MAIN PUBLICATIONS

1. ByMC: Byzantine Model Checker.
Igor Konnov, Josef Widder.
ISOLA 2018, pages 327-342, 2018. [ISOLA18]

1. Reachability in Parameterized Systems: All Flavors of Threshold Automata.
Jure Kukovec, Igor Konnov, Josef Widder.
CONCUR 2018, pages 19:1--19:17, 2018. [CONCUR18]

1. A short counterexample property for safety and liveness verification of fault-tolerant distributed algorithms.
Igor V. Konnov, Marijana Lazic, Helmut Veith, Josef Widder.
POPL 2017, 2017, pages 719-734, 2017. [POPL17]

1. Synthesis of Distributed Algorithms with Parameterized Threshold Guards.
Marijana Lazic, Igor Konnov, Josef Widder, Roderick Bloem.
OPODIS, volume 95 of LIPIcs, pages 32:1-32:20, 2017. [OPODIS17]

1. Para^2: Parameterized Path Reduction, Acceleration, and SMT for Reachability in Threshold-Guarded Distributed Algorithms.
Igor Konnov, Marijana Lazic, Helmut Veith, Josef Widder.
Formal Methods in System Design, volume 51, number 2, pages 270-307, 2017, Springer. [FMSD17]

1. On the completeness of bounded model checking for threshold-based distributed algorithms: Reachability.
Igor V. Konnov, Helmut Veith, Josef Widder.
Information and Computation, volume 252, pages 95-109, 2017. [INFCOMP17]

1. SMT and POR beat Counter Abstraction: Parameterized Model Checking of Threshold-Based Distributed Algorithms.
Igor Konnov, Helmut Veith, Josef Widder.
CAV (Part I), volume 9206 of LNCS, pages 85-102, 2015. [CAV15]

1. On the Completeness of Bounded Model Checking for Threshold-Based Distributed Algorithms: Reachability.
Igor Konnov, Helmut Veith, Josef Widder.
CONCUR 2014, volume 8704 of LNCS, pages 125-140, 2014. [CONCUR14]

1. Parameterized model checking of fault-tolerant distributed algorithms by abstraction.
Annu John, Igor Konnov, Ulrich Schmid, Helmut Veith, Josef Widder.
FMCAD, pages 201-209, 2013. [FMCAD13]

[ISOLA18]: https://hal.inria.fr/hal-01909653
[CONCUR18]: https://doi.org/10.4230/LIPIcs.CONCUR.2018.19
[OPODIS17]: https://doi.org/10.4230/LIPIcs.OPODIS.2017.32
[POPL17]: http://forsyte.at/wp-content/uploads/popl17main-main116-p-9d29769-29971-final.pdf
[INFCOMP17]: http://dx.doi.org/10.1016/j.ic.2016.03.006
[FMSD17]: https://link.springer.com/article/10.1007/s10703-017-0297-4
[CAV15]: http://forsyte.at/download/konnov-cav15.pdf
[CONCUR14]: http://forsyte.at/wp-content/uploads/concur14-reachability.pdf
[FMCAD13]: http://www.cs.utexas.edu/users/hunt/FMCAD/FMCAD13/papers/10-Model-Checking-Fault-Tolerant-Distributed-Algo.pdf

