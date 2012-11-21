#include <iostream>
#include <string>
#include "pycudd.h"
#include "dddmp.h"
#include "epd.h"

using std::cerr;
using std::endl;

DdManager* mgr = NULL;
DdNode **node_iter = (DdNode **) malloc(sizeof(DdNode *));
int **cube_iter = (int **) malloc(sizeof(int *));
DdNode ***glob_conj = (DdNode ***) malloc(sizeof(DdNode **));

IntArray::IntArray(int size) {

  if (size < 0)
    sz = Cudd_ReadSize(mgr);
  else
    sz = size; 
  vec = new int[sz]; 
  memset( vec, 0, sz * sizeof(int));
}

IntArray::~IntArray() {
  delete [] vec;
}

void IntArray::AssignVect(int* cuddvec, int size) {
   
  sz = size; 
  delete [] vec;
  vec = new int[sz]; 
  memcpy( vec, cuddvec, sz * sizeof(int));
}

int IntCompareFunc(const void *s, const void *t) {
  return *((int *) s) - *((int *) t);
}

void IntArray::AssignComplVect(int* cuddvec, int size, int univ) {
  int *temp = new int[size+1];
  memcpy ( temp, cuddvec, size * sizeof(int));
  temp[size] = univ;
  qsort( temp, size, sizeof(int), IntCompareFunc);
  int *iptr = temp;
  sz = univ - size; 
  delete [] vec;
  vec = new int[sz]; 
  int *nptr = vec;
  for (int i=0; i < univ; i++) {
    if (i < *iptr) *nptr++ = i;
    else if ( i == *iptr) iptr++;
    else do {
      iptr++;
    } while( i > *iptr);
  }
}

StringArray::StringArray(int size) {
  sz = size; 
  vec = new char *[sz]; 
  memset( vec, 0, sz * sizeof(char *));
}

StringArray::~StringArray() {
  delete [] vec;
}

int StrCompareFunc(const void *s, const void *t) {
  return strcmp(*((char **) s), *((char **) t));
}

DoubleArray::DoubleArray(int size) {

  if (size < 0)
    sz = Cudd_ReadSize(mgr);
  else
    sz = size; 
  vec = new double[sz]; 
  for(int j=0; j<sz; j++) 
    vec[j] = 0; 
}

DoubleArray::~DoubleArray() {
  delete [] vec;
}

DdArray::DdArray(int size) { 

#ifdef PYCUDD_DEBUG
  cerr << endl << "Constructor for DdArray called" << endl;
#endif
  if (size < 0)
    sz = Cudd_ReadSize(mgr);
  else
    sz = size; 
  i = 0; 
  vec = new DdNode*[sz]; 
  for(int j=0; j<sz; j++) 
    vec[j] = NULL; 
}

DdArray::~DdArray() {  

#ifdef PYCUDD_DEBUG
  cerr << endl << "Deleting DdArray" << endl;
#endif
  if (mgr) {
     for(int j=0; j<sz; j++) {
       if(vec[j]!=NULL) 
         Cudd_RecursiveDeref(mgr,vec[j]); 
       vec[j] = NULL;
     }
  } 
  delete [] vec; 
}

DdNode*
DdArray::Pop() {
  if (i!=0) {
    DdNode* result=vec[--i]; 
    vec[i]=NULL; 
    if (result!=NULL) Cudd_RecursiveDeref(mgr,result); 
    return result;
  }
  return NULL;
}

void
DdArray::Push(DdNode* val) { 
  if (i<sz) { 
    if (vec[i]!=NULL) Cudd_RecursiveDeref(mgr,vec[i]);
    vec[i++]=val; 
    Cudd_Ref(val); 
  } 
}

DdNode* 
DdArray::And() { 
  DdNode *result;
  DdNode *tmp;
  int i;
 
  OrderVector(0, sz-1);
  result = vec[0];
  Cudd_Ref(result);

  for (i=1; i<sz; i++) {
    /* printf("BDD %d at level %d.\n",Cudd_NodeReadIndex(vec[i]),Cudd_ReadPerm(mgr,Cudd_NodeReadIndex(vec[i]))); */
    tmp = Cudd_bddAnd(mgr,vec[i],result);
    Cudd_Ref(tmp);
    Cudd_RecursiveDeref(mgr,result);
    result = tmp;
  }

  return result;
}
  
DdNode* 
DdArray::Or() {
  DdNode *tmp;
  DdNode *result;
  int i;
 
  OrderVector(0, sz-1);
  result = vec[0];
  Cudd_Ref(result);

  for (i=1; i<sz; i++) { 
    tmp = Cudd_bddOr(mgr,vec[i],result);
    Cudd_Ref(tmp);
    Cudd_RecursiveDeref(mgr,result);
    result = tmp;
  }

  return result;
}

DdNode*
DdArray::AtLeastN(int n) {

  int i,j;
  DdNode** temp;
  DdNode* tmp;
  int max_width = sz - (--n);

  if ( max_width <= 0 ) {
    tmp = Cudd_ReadLogicZero(mgr);
    Cudd_Ref(tmp);
    return tmp;
  }

  OrderVector(0, sz-1);

  temp = ALLOC(DdNode *,max_width);

  for ( i=0; i< max_width; i++) {
    temp[i] = Cudd_ReadOne(mgr);
    Cudd_Ref(temp[i]);
  }

  for (i=0; i<=n; i++) {
    tmp = Cudd_bddIte(mgr, vec[i], temp[0], Cudd_ReadLogicZero(mgr));
    Cudd_Ref(tmp);
    Cudd_RecursiveDeref(mgr,temp[0]);
    temp[0]= tmp;

    for( j=1; j < max_width; j++) { 
      tmp = Cudd_bddIte( mgr, vec[i+j], temp[j], temp[j-1]);
      Cudd_Ref(tmp);
      Cudd_RecursiveDeref(mgr,temp[j]);
      temp[j]= tmp;
    }
  }

  tmp = temp[max_width-1];
  for ( i=0; i<max_width-1; i++)
    Cudd_RecursiveDeref(mgr, temp[i]);

  FREE(temp);

  return tmp;
}

DdNode*
DdArray::UpToN( int n ) {

  int i,j;
  DdNode** temp;
  DdNode* tmp;
  int max_width = sz-n;

  if ( max_width <= 0 ) {
    tmp = Cudd_ReadOne(mgr);
    Cudd_Ref(tmp);
    return tmp;
  }

  OrderVector(0, sz-1);

  temp = ALLOC(DdNode *,max_width+1);

  for ( i=0; i< max_width; i++) {
    temp[i] = Cudd_ReadLogicZero(mgr);
    Cudd_Ref(temp[i]);
  }

  temp[max_width] = Cudd_ReadOne(mgr);
  Cudd_Ref(temp[max_width]);

  for ( i=n; i>=0; i--)
    for( j=max_width-1 ; j >= 0; j--) {
      tmp = Cudd_bddIte( mgr, vec[sz-i-j-1], temp[j], temp[j+1]);
      Cudd_Ref(tmp);
      Cudd_RecursiveDeref(mgr,temp[j]);
      temp[j]= tmp;
    }
     
  tmp = temp[0];
  for ( i=1; i<=max_width; i++)
    Cudd_RecursiveDeref(mgr, temp[i]);

  FREE(temp);

  return tmp;
}

void
DdArray::SwapNodes( int i, int j) {
  DdNode *tmp = vec[i];
  vec[i] = vec[j];
  vec[j] = tmp;
}  

DdNode*
DdArray::ExactlyN( int n ) {

  int i,j;
  DdNode** temp;
  DdNode* tmp;
  int max_width = sz-(--n);

  if ( max_width <= 0 ) {
    tmp = Cudd_ReadLogicZero(mgr);
    Cudd_Ref(tmp);
    return tmp;
  }

  OrderVector(0, sz-1);

  temp = ALLOC(DdNode *,max_width);

  temp[0] = Cudd_ReadOne(mgr);
  Cudd_Ref(temp[0]);

  for ( i=1; i< max_width; i++) {
    temp[i] = Cudd_bddIte( mgr, vec[i-1], Cudd_ReadLogicZero(mgr), temp[i-1]);
    Cudd_Ref(temp[i]);
  }

  for (i=0; i<=n; i++) {
    tmp = Cudd_bddIte( mgr, vec[i], temp[0], Cudd_ReadLogicZero(mgr));
    Cudd_Ref(tmp);
    Cudd_RecursiveDeref(mgr,temp[0]);
    temp[0]= tmp;
    for( j=1; j < max_width; j++) {
      tmp = Cudd_bddIte( mgr, vec[i+j], temp[j], temp[j-1]);
      Cudd_Ref(tmp);
      Cudd_RecursiveDeref(mgr,temp[j]);
      temp[j]= tmp;
    }
  }

  tmp = temp[max_width-1];
  for ( i=0; i<max_width-1; i++)
    Cudd_RecursiveDeref(mgr, temp[i]);
  FREE(temp);

  return tmp;
}

DdNode*
DdArray::Constraint(int low, int high) {

  DdNode* result;
  DdNode* lr;
  DdNode* hr;

  if (low > high) {
    result = Cudd_ReadLogicZero(mgr);
    Cudd_Ref(result);
    return result;
  }

  if (low==high) return ExactlyN(low);

  if (low > 0) {
    lr = AtLeastN(low);
  } else {
    lr = Cudd_ReadOne(mgr);
    Cudd_Ref(lr);
  }

  if (high < sz) {
    hr = UpToN(high);
  } else {
    hr = Cudd_ReadOne(mgr);
    Cudd_Ref(hr);
  }

  result = Cudd_bddAnd(mgr,lr,hr);

  Cudd_Ref(result);

  Cudd_RecursiveDeref(mgr,lr);
  Cudd_RecursiveDeref(mgr,hr);

  return result;
}

DdNode*
DdArray::Compose(DdNode* term) { 
  if (sz != Cudd_ReadSize(mgr)) {
    cerr << "Can't compose without representative bdd for each index in the vector\n" << sz << "  " << Cudd_ReadSize(mgr);
    return term;
  }
  DdNode* result = Cudd_bddVectorCompose(mgr, term, vec);
  Cudd_Ref(result);
  return result;
}

void
DdArray::Fill(int offset, int mod) {

  int j=offset;
  for (int i=0; i<sz; i++,j+=mod) 
      __setitem__(i,Cudd_bddIthVar(mgr,j));
}

void
DdArray::FillWithIntArray( IntArray *a) {
  delete [] vec;
  sz = a->__len__();
  vec = new DdNode*[sz]; 
  for(int j=0; j<sz; j++) 
    vec[j] = Cudd_bddIthVar(mgr,a->vec[j]);
}

void
DdArray::OrderVector( int left, int right ) {

  DdNode* tmp;
  int last;
  int i;

  if (left >= right) return;
  tmp=vec[left]; vec[left]=vec[(left+right)/2]; vec[(left+right)/2]=tmp;
 
  last = left;

  for (i=left+1; i<=right; i++)
    if ( Cudd_ReadPerm(mgr,Cudd_NodeReadIndex(vec[i])) > Cudd_ReadPerm(mgr,Cudd_NodeReadIndex(vec[left]))) {
      ++last;
      tmp=vec[last]; vec[last]=vec[i]; vec[i]=tmp;

    }
  tmp=vec[left]; vec[left]=vec[last]; vec[last]=tmp;
  OrderVector( left,   last-1 );
  OrderVector( last+1, right );
}

void
DdArray::SupportVector( DdNode* term ) {
  DdNode *support = Cudd_Support(mgr, term);
  Cudd_Ref(support);
  sz = Cudd_DagSize(support)-1;
  delete [] vec;
  vec = new DdNode*[sz]; 
  memset( vec, 0, sz * sizeof(DdNode*));
  int vectindex = 0;
  while ((support != Cudd_Regular(Cudd_ReadOne(mgr))) && (support != Cudd_Regular(Cudd_ReadZero(mgr)))) {
    int nodeindex = Cudd_NodeReadIndex(support);
    __setitem__(vectindex++,Cudd_bddIthVar(mgr,nodeindex));
    DdNode *tmp = Cudd_Regular(Cudd_T(support));
    if ((tmp == Cudd_Regular(Cudd_ReadOne(mgr))) || (tmp == Cudd_Regular(Cudd_ReadZero(mgr))))
      support = Cudd_Regular(Cudd_E(support));
    else
      support = tmp;
  }
}

int
DdArray::SetVarMap( DdArray* other ) {
  if (sz != other->sz)
    return 0;
  return Cudd_SetVarMap(mgr,vec,other->vec,sz);
}

DdNode*
DdArray::VectorSupport() {
  DdNode* result = Cudd_VectorSupport(mgr,vec,sz); 
  Cudd_Ref(result); 
  return result; 
}

int
DdArray::VectorSupportIndex(int **dum_sup) {
  *dum_sup = Cudd_VectorSupportIndex(mgr,vec,sz);
  if (*dum_sup == NULL) return 0;
  else return 1;
}

DdNode*
DdArray::PickOneMinterm( DdNode* term ) {
  DdNode *result;
  result = Cudd_bddPickOneMinterm(mgr,term,vec,sz);
  Cudd_Ref(result);
  return result;
}

DdNode* 
DdArray::HoldTR( DdArray* other ) {
  DdNode *tmp1,*tmp2;
  DdNode *result;
  int i;
 
  result = Cudd_bddXnor(mgr,vec[0],other->vec[0]);
  Cudd_Ref(result);

  for (i=1; i<sz; i++) { 
    tmp1 = Cudd_bddXnor(mgr,vec[i],other->vec[i]);
    Cudd_Ref(tmp1);
 
    tmp2 = Cudd_bddAnd(mgr,result,tmp1);
    Cudd_Ref(tmp2);
    Cudd_RecursiveDeref(mgr,result);
    Cudd_RecursiveDeref(mgr,tmp1);
    result = tmp2;
  }

  return result;
}

int
DdArray::Find( DdNode* term ) {
  for (DdNode **cptr=vec; cptr < vec+sz; cptr++)
    if (*cptr == term) return 1;
  return 0;
}

int
DdArray::Save( char* filename ) {

  return Dddmp_cuddBddArrayStore(mgr,
				 NULL,
				 sz,
				 vec,
				 NULL,
				 NULL,
				 NULL,
				 DDDMP_MODE_BINARY,
				 DDDMP_VARDEFAULT,
				 filename,
				 NULL);
}

int
DdArray::SaveText( char* filename ) {

  return Dddmp_cuddBddArrayStore(mgr,
				 NULL,
				 sz,
				 vec,
				 NULL,
				 NULL,
				 NULL,
				 DDDMP_MODE_TEXT,
				 DDDMP_VARDEFAULT,
				 filename,
				 NULL);
}

int
DdArray::Load( char* filename ) {
  delete [] vec;
  vec = new DdNode*[ 1024];
  int roots = Dddmp_cuddBddArrayLoad(mgr,
				     DDDMP_ROOT_MATCHLIST,
				     NULL,
				     DDDMP_VAR_MATCHIDS,
				     NULL,
				     NULL,
				     NULL, 
				     DDDMP_MODE_BINARY,
				     filename,
				     NULL,
				     &vec);
  sz = roots;
  DdNode **p = new DdNode*[ sz];  
  memcpy( p, vec, sz * sizeof( DdArray *));
  delete [] vec;
  vec = p;
  return roots;
}


int
DdArray::LoadText( char* filename ) {

  if (sz != 0)
    return -1;
  
  delete [] vec;

  int roots = Dddmp_cuddBddArrayLoad(mgr,
				     DDDMP_ROOT_MATCHLIST,
				     NULL,
				     DDDMP_VAR_MATCHIDS,
				     NULL,
				     NULL,
				     NULL, 
				     DDDMP_MODE_TEXT,
				     filename,
				     NULL,
				     &vec);

  if (roots > 0)
    sz = roots;

  return roots;

}

int 
DdArray::ArrayLoad( int rootmatchmode, StringArray *rootmatchnames, int varmatchmode, 
	       StringArray *varmatchnames, IntArray *varmatchauxids, 
	       IntArray *varcomposeids, int mode, char *filename, FILE *fp) 
{ 
  int roots = Dddmp_cuddBddArrayLoad( mgr, (Dddmp_RootMatchType) rootmatchmode, 
				 (char **) ( rootmatchnames ? rootmatchnames->vec : NULL), 
				 (Dddmp_VarMatchType) varmatchmode, 
				 (char **) ( varmatchnames ? varmatchnames->vec : NULL), 
				 (int *) ( varmatchauxids ? varmatchauxids->vec : NULL), 
				 (int *) ( varcomposeids ? varcomposeids->vec : NULL), 
				 mode, filename, fp, &vec); 
  return roots;
}
int 
DdArray::ArrayStore( char *ddname, StringArray *rootnames, StringArray *varnames, IntArray *auxids, 
		     int mode, int varinfo, char *filename, FILE *fp) 
{ 
  int roots =  Dddmp_cuddBddArrayStore( mgr, ddname, sz, vec, 
				  (char **) ( rootnames ? rootnames->vec : NULL), 
				  (char **) ( varnames ? varnames->vec : NULL), 
				  (int *) ( auxids ? auxids->vec : NULL), mode, 
				  (Dddmp_VarInfoType) varinfo, filename, fp); 
  return roots;
}
