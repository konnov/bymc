%{
#ifndef FROM_PYCUDDI
#error Use only from pycudd.i. Make sure to define FROM_PYCUDDI!
#endif
%}

// Return the clauses as (valid?, (var1,phase1), (var2,phase2))
%typemap (argout) (DdHalfWord *dum_var1, DdHalfWord *dum_var2, int *dum_phase1, int *dum_phase2) {
  PyObject *o, *o2, *o3;
  o2 = $result;
  $result = PyTuple_New(3);
  PyTuple_SetItem($result,0,o2);

  o3 = PyTuple_New(2);
  if (*$1 == CUDD_MAXINDEX) o = PyInt_FromLong(-1);
  else o = PyInt_FromLong(*$1);
  PyTuple_SetItem(o3,0,o);
  o = PyInt_FromLong(*$3);
  PyTuple_SetItem(o3,1,o);
  PyTuple_SetItem($result,1,o3);

  o3 = PyTuple_New(2);
  if (*$2 == CUDD_MAXINDEX) o = PyInt_FromLong(-1);
  else o = PyInt_FromLong(*$2);
  PyTuple_SetItem(o3,0,o);
  o = PyInt_FromLong(*$4);
  PyTuple_SetItem(o3,1,o);
  PyTuple_SetItem($result,2,o3);

  Py_DECREF(o2);
}


%typemap(in,numinputs=0) DdHalfWord *dum_var1 (DdHalfWord dv1) {
  $1 = &dv1;
}

%typemap(in,numinputs=0) DdHalfWord *dum_var2 (DdHalfWord dv2) {
  $1 = &dv2;
}

struct DdTlcInfo { };

%extend DdTlcInfo {
%pythoncode %{
__doc__ = "Helper class for enumeration of two literal clauses. Look at example2.py for usage."
%}
  DdTlcInfo() {
    return NULL;
  }

  ~DdTlcInfo() {
    Cudd_tlcInfoFree(self);
  }
  %apply int *OUTPUT { int * dum_phase1 }
  %apply int *OUTPUT { int * dum_phase2 }
  int ReadIthClause(int i, DdHalfWord *dum_var1, DdHalfWord *dum_var2, int *dum_phase1, int *dum_phase2) { return Cudd_ReadIthClause(self, i, dum_var1, dum_var2, dum_phase1, dum_phase2); }
}

 
