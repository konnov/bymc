/////////////////////////////////////////////////
//
// extern declarations used to make the typemaps work
// Note that the extern declaration for the default manager comes from pycudd.h
//
/////////////////////////////////////////////////

%{
extern DdNode ***glob_conj;
extern DdNode **node_iter;    
extern int **cube_iter;
%}
