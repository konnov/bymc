%include docstring.h
%module(docstring=DOCSTRING) pycudd
/***************

   PYCUDD - SWIG base Python inteface wrapper of CUDD ( University of Colorado fast BDD package)

   Copyright (c) 2002 University of California, Santa Barbara

   Thou must always include this copyright notice with the code.

   The pycudd wrapper is copyrighted primarily to protect all users of the
   code. i.e. you cannot use the code in a package which you then patent or
   otherwise claim proprietary use of in a way which would restrict another
   user from using the code we distribute for his purposes. You can use the
   code as part of your own proprietary software as long as the copyright
   labels remain on the part of the software distributed by us. 
****************/

%{
#include <iostream>
#include <iomanip>
#include <cassert>
#include <string>
using std::cerr;
using std::endl;
using std::hex;
using std::string;

#include "cudd.h"
#include "pycudd.h"
#include "dddmp.h"
#include "epd.h"
#ifdef BREL_R_THERE
#include "brelInt.h"
#endif
#define FROM_PYCUDDI
%}

#if SWIG_VERSION >= 0x010328
%pythonnondynamic;
#elif SWIG_VERSION >= 0x010323
// This prevents run-time addition of components to the PyCUDD classes.
%pythonnondynamic(1);
#endif

%include externs.i    // externs needed for the typemaps in utils.i
%include utils.i      // utils.i contains all the various typemaps used

%include pycudd.h     // Provides classes IntArray, DoubleArray, StringArray and DdArray

#ifdef BREL_R_THERE   // Rudimentary BREL wrapper -- currently only provides BrelContext 
%include brel.i       // and BrelRelation in a limited fashion
#endif

/* FIXME: Add attributes and methods */
struct MtrNode { };

#if CUDDVER >= 0x020400    // If you have CUDD 2.4.0, this enables enumeration of two literal clauses
%include tlcinfo.i
#endif
%include epd.i
%include ddmanager.i  // Provides methods of DdManager
%include ddgen.i      // Provides DdGen -- not expected to be used externally
%include ddnode.i     // Provides DdNode, and if CUDD > 2.4.0, NodePair for prime enumeration
%include pyiter.i     // Python additions to support iteration over cubes/nodes/primes



