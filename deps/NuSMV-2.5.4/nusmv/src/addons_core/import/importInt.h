/**CHeaderFile*****************************************************************

  FileName    [importInt.h]

  PackageName [addons.import]

  Synopsis [The private internal header file of the
  <tt>import</tt> addon.]

  Description [The <tt>import</tt> implementation package]

  Author      [Igor Konnov]

  Copyright   [ ]

******************************************************************************/

#ifndef __IMPORT_INT_H__
#define __IMPORT_INT_H__

#include "import.h"

#include "dd/dd.h"
#include "opt/opt.h"
#include "compile/compile.h"
#include "compile/type_checking/TypeChecker.h"
#include "utils/NodeList.h"
#include "enc/bdd/BddEnc.h"
#include "utils/utils.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/
extern FILE* nusmv_stdout;
extern FILE* nusmv_stderr;
extern cmp_struct_ptr cmps;


/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/


#endif /* __IMPORT_H__ */
