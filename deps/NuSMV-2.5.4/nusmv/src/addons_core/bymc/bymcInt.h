/**CHeaderFile*****************************************************************

  FileName    [bymcInt.h]

  PackageName [addons.bymc]

  Synopsis [The private internal header file of the
  <tt>bymc</tt> addon.]

  Description [The <tt>bymc</tt> implementation package]

  Author      [Igor Konnov]

  Copyright   [ ]

******************************************************************************/

#ifndef __BYMC_INT_H__
#define __BYMC_INT_H__

#include "bymc.h"

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


#endif /* __BYMC_H__ */
