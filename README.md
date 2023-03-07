# ByMC: Byzantine Model Checker

This is a toolset for parameterized model checking of threshold-guarded fault-tolerant distributed algorithms.

## Status

The tool author [Igor Konnov](https://konnov.github.io/) is not developing it
anymore. If you want to see new cool projects, check
[Quint](https://github.com/informalsystems/quint/) and
[Apalache](https://github.com/informalsystems/apalache/).

## Publications

A recent survey of the techniques implemented in ByMC (and other tools) can
be found in the [paper at LMCS'23](https://lmcs.episciences.org/10824):

    Igor Konnov ; Marijana Lazić ; Ilina Stoilkovska ; Josef Widder -
    Survey on Parameterized Verification with Threshold Automata and the
    Byzantine Model Checker. Logical Methods in Computer Science, January 18,
    2023, Volume 19, Issue 1

Follow the references in the survey to learn more about the older techniques.

## Installation

**WARNING:** Since this tool is using libraries that go back to 2013, it is
getting harder to compile it. The easiest way to run ByMC is by downloading a
virtual machine and running the tool inside
[VirtualBox](https://www.virtualbox.org/). The latest version is
[ByMC 2.4.4](https://drive.google.com/file/d/1m1LNeCPbEdOE35KBsVSsICeXQi8FM8gq/view?usp=share_link) (at Google Drive).

## Next steps    

* To see the tool in action, read [the tutorial](./bymc/doc/tutorial.md).
* For installation instructions, check [README](./bymc/README.md) in the source directory. 
* To see the accompanying publications, visit the [tool website](https://forsyte.at/software/bymc/).

## Structure

The directory layout is as follows:

* ```bymc``` -- the scripts and tool source code
* ```plugins``` -- tool plugins

* ```legacy-bddc``` -- set of auxiliary scripts for model checking with NuSMV, needed only to run legacy techniques
* ```legacy-deps``` -- various dependencies required by the tools that are hard to install automatically, needed only to run legacy techniques
