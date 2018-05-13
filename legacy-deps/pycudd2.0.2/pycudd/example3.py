#!/usr/bin/python -i
# This example shows how to use the BREL interface
#

######################################
###
### NOTE: THIS IS STILL IN BETA
###
######################################
 
import pycudd
m = pycudd.DdManager()
m.SetDefault()

# Note how the DdArrays are created and initialised
ips = pycudd.DdArray(2)
ops=pycudd.DdArray(2)
a = m.IthVar(0)
b = m.IthVar(1)
c = m.IthVar(2)
d = m.IthVar(3)
ips.Push(a)
ips.Push(b)
ops.Push(c)
ops.Push(d)

#
# Create a relation -- this maps 00 -> 00, 11; 11 -> 01, 10; 01 -> --; 10 -> --
#
rel = (~a & ~b & ((~c & ~d) | (c & d))) | (a & b & ((~c & d) | (c & ~d)))
rel |= (~a & b)
rel |= (a & ~b)
print "The relation is"
rel.PrintMinterm()

# Create a BrelRelation_t object 
bbr = pycudd.BrelRelation_t(rel,ips,ops)
# Create a BREL Context -- more methods will be added to this class
ct = pycudd.BrelContext_t()
# Call the solver
z = bbr.SolveRelation(ct)

#
# The solution is returned as a DdArray, which contains functions for the onset of
# each minimised output. In our case, note how output 1 is reduced to always 0 --
# thus, the call to PrintMinterm doesn't produce any output
#
print "Output 0 is"
z[0].PrintMinterm()

print "Output 1 is"
z[1].PrintMinterm()
