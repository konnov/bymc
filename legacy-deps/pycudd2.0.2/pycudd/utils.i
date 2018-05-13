%{

#ifdef PYCUDD_DEBUG
#define using_map(x) printf("Entering typemap for %s\n",x);
#endif

/////////////////////////////////////////////
//
// This takes a PyObject * result that is assumed to be a long
// If it is 0, there is no array to convert in src, else, there
// is an array of sz elements to grab from there
//
/////////////////////////////////////////////

static PyObject * array_to_tuple(PyObject *dest, int **src, int sz) {
  PyObject *o2, *result;
  // Note: When adding o2 to the tuple using PyTuple_SetItem, Py_DECREF is not called, since
  // PyTuple_SetItem is one of a few functions that "steal" a reference (Python manual terminology)
  // What this means is that PyTuple_SetItem will take care of the DECREF when the tuple is destroyed
  int chk;
  int i;
  o2 = dest;
  chk = (int) PyInt_AsLong(o2);
  if (chk) {
    result = PyTuple_New(sz+1);
    PyTuple_SetItem(result,0,o2);
    for (i=0;i<sz;i++) PyTuple_SetItem(result,i+1,PyInt_FromLong((*src)[i]));
    // Note that DdGen will free the memory allocated for the int array 
  }
  else {
    result = PyTuple_New(1);
    PyTuple_SetItem(result,0,o2);
  }
  return result;
}
%}

///////////////////////////////////////////////////
//
// Typemaps dum_sup and dum_cube both use the variable
// int **cube_iter, defined in pycudd.cpp
//
/////////////////////////////////////////////////// 
///////////////////////////////////////////////////
//
// dum_sup is used to return arrays of ints where
// the array has to be freed by us.
// Used in     : DdNode.SupportIndex, DdArray.VectorSupportIndex
// Uses global : int **cube_iter, defined in pycudd.cpp
//
///////////////////////////////////////////////////

%typemap(argout) int **dum_sup {

#ifdef PYCUDD_DEBUG
  using_map("dum_sup")
#endif

  int sz = Cudd_ReadSize(mgr);
  int chk = (int) PyInt_AsLong($result);
  $result = array_to_tuple($result, $1, sz);
  if (chk) FREE(*$1);
}

%typemap(in,numinputs=0) int **dum_sup {
  $1 = cube_iter;
}

///////////////////////////////////////////////////
//
// dum_cube is used to return arrays of ints where the 
// array is freed by other means.
// Used by     : DdNode.FirstCube, DdNode.NextCube, DdNode.FirstPrime, DdNode.NextPrime
//               In all the above cases, the call to Cudd_GenFree at the end of
//               enumeration takes care of freeing the memory
// Uses global : int **cube_iter, defined in pycudd.cpp
//
///////////////////////////////////////////////////

%typemap(argout) int **dum_cube {

#ifdef PYCUDD_DEBUG
  using_map("dum_cube")
#endif

  int sz = Cudd_ReadSize(mgr);
  $result = array_to_tuple($result, $1, sz);
}

%typemap(in,numinputs=0) int **dum_cube {
  $1 = cube_iter;
}

///////////////////////////////////////////////////
// 
// dum_y is used to return a single DdNode *, given a 
// DdNode **. 
// Note: We have to ref the node we return!
// Used by     : DdNode.FirstNode, DdNode.NextNode
// Uses global : DdNode **node_iter, defined in pycudd.cpp
//
///////////////////////////////////////////////////

%typemap(argout) DdNode **dum_y {
  PyObject *o, *o2;

#ifdef PYCUDD_DEBUG
  using_map("dum_y")
#endif

  Cudd_Ref(*$1);
  o = SWIG_NewPointerObj(*$1,$descriptor(DdNode *),0);
  o2 = $result;
  $result = PyTuple_New(2);
  PyTuple_SetItem($result,0,o2);
  PyTuple_SetItem($result,1,o);
}

%typemap(in,numinputs=0) DdNode **dum_y {
  $1 = node_iter;
}

///////////////////////////////////////////////////
//
// dum_juncts is used to return a pair of DdNodes given a
// DdNode *** ie a pointer to an array of DdNode*
// Used by     : DdNode.ApproxConjDecompts, DdNode.ApproxDisjDecompts, DdNode.IterConjDecomp,
//               DdNode.IterDisjDecomp, DdNode.GenConjDecomp, DdNode.GenDisjDecomp,
//               DdNode.VarConjDecomp, DdNode.VarDisjDecomp
//               NOTE: None of the above funcs free the space for the array -- we do that
// Uses global : DdNode ***glob_conj, defined in pycudd.cpp
//
///////////////////////////////////////////////////

%typemap(argout) DdNode ***dum_juncts {
  int num_nds;
  PyObject *o, *o2;

#ifdef PYCUDD_DEBUG
  using_map("dum_juncts")
#endif

  num_nds = (int) PyInt_AsLong($result);
  if (num_nds == 1) {
    o = SWIG_NewPointerObj(**$1,$descriptor(DdNode *),0);
    o2 = $result;
    $result = PyTuple_New(2);
    PyTuple_SetItem($result,0,o2);
    PyTuple_SetItem($result,1,o);
  }
  if (num_nds == 2) {
    o2 = $result;
    $result = PyTuple_New(3);
    PyTuple_SetItem($result,0,o2);
    o = SWIG_NewPointerObj((*$1)[0],$descriptor(DdNode *),0);
    PyTuple_SetItem($result,1,o);
    o = SWIG_NewPointerObj((*$1)[1],$descriptor(DdNode *),0);
    PyTuple_SetItem($result,2,o);
  }
  // The storage for the con/dis juncts is NOT freed by CUDD -- we have to do it
  FREE(*$1);
}

%typemap(in,numinputs=0) DdNode ***dum_juncts {
  $1 = glob_conj;
}

