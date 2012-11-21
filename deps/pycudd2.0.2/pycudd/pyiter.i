//////////////////////////////////////////////
//
// This file contains the neat shots of python code needed to get the various
// iterators working. The iterators themselves are created by DdNode or NodePair
//
//////////////////////////////////////////////

#if CUDDVER >= 0x020400
%pythoncode %{
cudd_version = 0x020400
%}
#else
%pythoncode %{
cudd_version = 0
%}
#endif


%pythoncode %{
###############################
#
# iter_meth is used to set, surprise, the iteration method for DdNodes
# 0 -- over cubes
# 1 -- over nodes
# 2 -- over primes
# Note that iteration over primes is only available in CUDD >= 2.4.0
#
################################
iter_meth = 0

def set_iter_meth(meth,verbose = False):
  global iter_meth
  methods = ["cubes", "nodes", "primes"]
  if verbose:
      print "Setting iter method to iterate over ",methods[meth]
  iter_meth = meth

class ForeachCubeIterator:
    def __init__(self,Dd):
        self.gen = DdGen(Dd,iter_meth)
        self.node = Dd
        self.done = 0
        self.ret_val = Dd.FirstCube(self.gen)
        if not self.ret_val[0]: self.done = 1
        
    def __iter__(self):
        return self

    def next(self):
        if self.done: raise StopIteration
        to_ret = self.ret_val[1:]
        self.ret_val = self.node.NextCube(self.gen)
        if not self.ret_val[0]:
	    self.done = 1
        return to_ret

class ForeachNodeIterator:
    def __init__(self,Dd):
        self.gen = DdGen(Dd,iter_meth)
        self.node = Dd
        self.done = 0
        self.ret_val = Dd.FirstNode(self.gen)
        if not self.ret_val[0]: self.done = 1
        
    def __iter__(self):
        return self

    def next(self):
        if self.done: raise StopIteration
        to_ret = self.ret_val[1]
        self.ret_val = self.node.NextNode(self.gen)
        if not self.ret_val[0]:
            self.done = 1
        return to_ret

class ForeachPrimeIterator:
    def __init__(self,npair):
        global cudd_version
        if cudd_version < 0x020400:
            print "CUDD versions < 2.4.0 do not support iteration over primes"
            raise RuntimeError
        self.gen = DdGen(npair.LOWER(), iter_meth, npair.UPPER())
        self.npair = npair
        self.done = 0
        self.ret_val = npair.FirstPrime(self.gen)
        if not self.ret_val[0]: self.done = 1
    def __iter__(self):
        return self

    def next(self):
        if self.done: raise StopIteration
        to_ret = self.ret_val[1:]
        self.ret_val = self.npair.NextPrime(self.gen)
	if not self.ret_val[0]:
            self.done = 1
        return to_ret

def cube_tuple_to_str(cube_tup):
    res = ""
    for char in cube_tup:
        if char == 2: res += '-'
        else: res += str(char)
    return res
%}
