
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
 * ocamlgraph: http://ocamlgraph.lri.fr/
 * ocamlunit (if you want to run unit tests)
 * yices 1.x: http://yices.csl.sri.com/download.shtml
 * at least one of those:
     - spin: http://spinroot.com/spin/Man/README.html#S2
     - nusmv: http://nusmv.fbk.eu/NuSMV/download/getting-v2.html
     - faster: http://www.lsv.ens-cachan.fr/Software/fast/
 * lingeling: http://fmv.jku.at/lingeling/
     (if you want to run bounded model checking using lingeling)
 * gcc (if you are going to use spin)
 * pycudd (Sec. 6, if you want to compute the bounds on the diameter or
           check the algorithms with FASTer)

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

4.1. SPIN

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


4.2. NuSMV with BDDs

Parameterized model checking with the abstraction-refinement:

./verifypa-nusmv-bdd ${benchmarks}/bcast-byz.pml relay


4.3. NuSMV with BMC

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


4.4 NuSMV with FAST    

./verifypa-fast --plugin <fast-plugin> ${benchmarks}/bcast-byz.pml unforg


4.5 COMPUTING DIAMETER (of PIA data abstraction)

./analyse ${benchmarks}/bcast-byz.pml bounds

gives bounds on the diameter of counter systems and counter abstractions


5. HOW TO INSTALL OCAML AND THE LIBRARIES?

The easiest way to install the dependencies is to use your package manager,
i.e., apt-get, zypper, etc. For instance, this tool is periodically built
on Debian Wheezy, which makes all the libraries available via its package
manager apt-get.

If you do not have ocaml and the required ocaml packages, consider using
ocamlbrew: http://opam.ocaml.org/doc/Quick_Install.html#h4-Usingocamlbrew

Ocamlbrew bootstraps the whole ocaml infrastructure together with the package
manager called opam. As soon as opam is in place, you can install the
packages as follows:

$ opam install ounit ocamlgraph

(Do not forget to include the line
'source ~/ocamlbrew/ocaml-4.00.1/etc/ocamlbrew.bashrc'
in your ~/.bashrc or ~/.zshrc before doing that)

6. INSTALLING PYCUDD

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

