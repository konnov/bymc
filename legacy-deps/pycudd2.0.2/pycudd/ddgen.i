%{
#ifndef FROM_PYCUDDI
#error Use only from pycudd.i. Make sure to define FROM_PYCUDDI!
#endif
%}

// These should not have to be called by the user

struct DdGen { } ;

%extend DdGen {
%pythoncode{
__doc__ = "Not expected to be used directly."
}
  DdGen(DdNode *node1, int method, DdNode *node2=NULL) {
    CUDD_VALUE_TYPE val;
    DdGen *result;
    if (method == 0) result = Cudd_FirstCube(mgr, node1, cube_iter, &val); 
    else if (method == 1) result = Cudd_FirstNode(mgr, node1, node_iter); 
#if CUDDVER >= 0x020400

    else if (method == 2) {
      assert(node2 != NULL);
      result = Cudd_FirstPrime(mgr,node1,node2, cube_iter);
    }
#endif

#ifdef PYCUDD_DEBUG 
    fprintf(Cudd_ReadStdout(mgr),"Generator %d was created\n",result); 
#endif
    return result;
  }

  ~DdGen() {
    Cudd_GenFree(self);
#ifdef PYCUDD_DEBUG
    fprintf(Cudd_ReadStdout(mgr),"Generator %d was freed\n",self);
#endif
  }
}
