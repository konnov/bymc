#!/usr/bin/python -i
## Change above to point to your python. The -i option leaves you in interactive mode after the script has completed. Use ctrl-d to exit python.

## Import the pycudd module
import pycudd

##
## The next two steps are essential. PyCUDD has been set up so that the multitudinous
## references to the DdManager are obviated. To achieve this, there is the notion of
## a default manager. Though you may have as many DdManager objects as you want, only
## one of them is active at any given point of time. All operations that require a
## manager use the manager that last called the SetDefault method. 
## 
## NOTE: The DdManager constructor takes the same arguments as Cudd_Init. Refer ddmanager.i
## to see the default values (which can be overriden when you call it)
##
mgr = pycudd.DdManager()
mgr.SetDefault()


## This simple example finds the truths set of f = (f0 | f1) & f2 where
## f0 = (x4 & ~x3) | x2
## f1 = (x3 & x1) | ~x0
## f2 = ~x0 + ~x3 + x4
## and x0 through x4 are individual Boolean variables

## Create bdd variables x0 through x4
x0 = mgr.IthVar(0)
x1 = mgr.IthVar(1)
x2 = mgr.IthVar(2)
x3 = mgr.IthVar(3)
x4 = mgr.IthVar(4)

## Compute functions f0 through f2
f0 = (x4 & ~x3) | x2
f1 = (x3 & x1) | ~x0
f2 = ~x0 + ~x3 + x4

## Compute function f
f = (f0 | f1) & f2

## Print the truth set of f
f.PrintMinterm()


