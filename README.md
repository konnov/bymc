# ByMC: Byzantine Model Checker

This is a toolset for parameterized model checking of threshold-guarded fault-tolerant distributed algorithms.

* To see the tool in action, read [the tutorial](./bymc/doc/tutorial.md).
* For installation instructions, check [README](./bymc/README.md) in the source directory. 
* To see the accompanying publications, visit the [tool website](https://forsyte.at/software/bymc/).

The directory layout is as follows:

* ```bymc``` -- the scripts and tool source code
* ```plugins``` -- tool plugins

* ```legacy-bddc``` -- set of auxiliary scripts for model checking with NuSMV, needed only to run legacy techniques
* ```legacy-deps``` -- various dependencies required by the tools that are hard to install automatically, needed only to run legacy techniques


Shall you have any questions, ask Igor Konnov ```<konnov at forsyte.at>```