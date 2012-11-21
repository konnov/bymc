#ifndef PYCUDD_H
#define PYCUDD_H

#include "util.h"
#include "cudd.h"
#include "cuddInt.h"
#include "dddmp.h"
extern DdManager* mgr;

#ifdef SWIG
%feature("autodoc","1");
#endif

// Exception class
class RangeError {};

class DdArray;

class IntArray {

  int sz;

 public:
  int* vec;
  IntArray(int size);  
  ~IntArray();
  void AssignVect( int *str, int size);
  void AssignComplVect( int *str, int size, int univ);
  int **ArrayAddress() { return &vec; }

#ifdef SWIG
%exception {
  try {
    $function
  }
  catch (RangeError x) {
    PyErr_SetString(PyExc_IndexError,"index out-of-bounds");
    return NULL;
  }
}
#endif
  int __getitem__(int j) { 
    if (j<sz && j>=0) return vec[j];
    throw RangeError(); 
  };
  void __setitem__(int j, int val) { 
    if (j<sz && j>=0) vec[j]=val;
    else throw RangeError(); 
  };
  int __len__() { return sz; }
  void Assign( int *list, int k) {
    if (k > sz) throw RangeError();
    for (int i=0; i < k; i++) vec[i] = list[i];
  }
  void Swap( int i, int j) {
    if (i<sz && i>=0 && j<sz && j>=0) {
      int tmp = vec[i];
      vec[i] = vec[j];
      vec[j] = tmp;
    }
    else throw RangeError();
  }
#ifdef SWIG
  %exception;
#endif

};

class StringArray {
  int sz;

 public:
  char** vec;
  StringArray(int size);  
  ~StringArray();
  char ***ArrayAddress() { return &vec; }

#ifdef SWIG
%exception {
  try {
    $function
  }
  catch (RangeError x) {
    PyErr_SetString(PyExc_IndexError,"index out-of-bounds");
    return NULL;
  }
}
#endif

  char * __getitem__(int j) { 
    if (j<sz && j>=0) return vec[j]; 
    throw RangeError(); 
  };
  void __setitem__(int j, char *val) {
    if (j<sz && j>=0) vec[j]=val;
    else throw RangeError(); 
  };
  int __len__() { return sz; }
  void Assign( char **list, int k) {
    if (k > sz) throw RangeError();
    for (int i=0; i < k; i++) vec[i] = list[i];
  }
  void Swap( int i, int j) {
    if (i<sz && i>=0 && j<sz && j>=0) {
      char *tmp = vec[i];
      vec[i] = vec[j];
      vec[j] = tmp;
    }
    else throw RangeError();
  }

#ifdef SWIG
%exception;
#endif

};

class DoubleArray {
  int sz;

 public:
  double* vec;
  DoubleArray(int size);
  ~DoubleArray();

#ifdef SWIG
%exception {
  try {
    $function
  }
  catch (RangeError x) {
    PyErr_SetString(PyExc_IndexError,"index out-of-bounds");
    return NULL;
  }
}
#endif

  double __getitem__(int j) { 
    if (j<sz && j>=0) return vec[j]; 
    throw RangeError(); 
  };
  void __setitem__(int j, double  val) { 
    if (j<sz && j>=0) vec[j]=val;
    else throw RangeError(); 
  };
  void Assign( double *list, int k) {
    if (k > sz) throw RangeError();
    for (int i=0; i < k; i++) vec[i] = list[i];
  }
  void Swap( int i, int j) {
    if (i<sz && i>=0 && j<sz && j>=0) {
      double tmp = vec[i];
      vec[i] = vec[j];
      vec[j] = tmp;
    }
    else throw RangeError();
  }

#ifdef SWIG
%exception;
#endif

};

class DdArray {
#ifdef SWIG
%pythoncode %{
__doc__ = "This class provides an array of DdNodes. This is an addition to the CUDD package. Create a DdArray by calling the constructor with the length of the array. In terms of Python array-like behaviour, you can index it, assign individual elements and take its length. Typically, these arrays are populated via the Push method. Refer pycudd.h and pycudd.cpp for function details.<br>"
%}
#endif

  int i;

public:
  int sz;
  DdNode** vec;
  DdArray(int size);
  ~DdArray();

#ifdef SWIG
%exception {
  try {
    $function
  }
  catch (RangeError x) {
    PyErr_SetString(PyExc_IndexError,"index out-of-bounds");
    return NULL;
  }
}
#endif

  DdNode* __getitem__(int j) {
    DdNode* result = NULL;
    if (j<sz && j>=0) { 
      result = vec[j];
      Cudd_Ref(result);
    }
    else throw RangeError();
    return result;
  };
  void __setitem__(int j, DdNode* val) { 
    if (j<sz && j>=0) { 
      if (vec[j]!=NULL) Cudd_RecursiveDeref(mgr,vec[j]);
      vec[j]=val;
      Cudd_Ref(vec[j]);
    }
    else throw RangeError();
  };
  int __len__() { return sz; }
  void Swap( int i, int j) {
    if (i<sz && i>=0 && j<sz && j>=0) {
      DdNode *tmp = vec[i];
      vec[i] = vec[j];
      vec[j] = tmp;
    }
    else throw RangeError();
  }

#ifdef SWIG
%exception;
#endif

  DdNode* Pop();
  DdNode* And();
  DdNode* Or();
  DdNode* AtLeastN(int n);
  DdNode* ExactlyN(int n);
  DdNode* UpToN(int n);
  DdNode* Constraint(int low, int high);
  DdNode* Compose(DdNode* term);
  void Assign( DdNode** list, int k) {
    if (k > sz) throw RangeError();
    for (int i=0; i < k; i++) { vec[i] = list[i]; }
  }
  void Push(DdNode* val);
  void SwapNodes( int i, int j);
  void Fill(int offset, int mod);
  void FillWithIntArray( IntArray *t);
  void OrderVector(int left, int right);
  void SupportVector(DdNode* term);
  int SetVarMap(DdArray* other);
  DdNode* VectorSupport();
  int VectorSupportIndex(int **dum_sup);
  DdNode* PickOneMinterm( DdNode* term );
  DdNode* HoldTR( DdArray* other );  
  int Find( DdNode* term);
  int Save( char* filename );
  int SaveText( char* filename );
  int Load( char* filename );
  int LoadText( char* filename );
  int ArrayLoad( int rootmatchmode, StringArray *rootmatchnames, int varmatchmode, 
		 StringArray *varmatchnames, IntArray *varmatchauxids, IntArray *varcomposeids, 
		 int mode, char *filename, FILE *fp=NULL);
  int ArrayStore( char *ddname, StringArray *rootnames, StringArray *varnames, IntArray *auxids, 
		  int mode, int varinfo, char *filename, FILE *fp=NULL);
};
  
#endif // PYCUDD_H
