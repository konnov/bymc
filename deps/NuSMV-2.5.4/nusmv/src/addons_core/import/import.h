/**CHeaderFile*****************************************************************

  FileName    [import.h]

  PackageName [addons.import]

  Synopsis    [The header file of the <tt>compass</tt> addon.]

  Description [The <tt>compass</tt> implementation package]

  Author      [Igor Konnov]

******************************************************************************/

#ifndef __IMPORT_H__
#define __IMPORT_H__

#include "utils/utils.h"
#include "enc/bdd/BddEnc.h"
#include "fsm/bdd/BddFsm.h"
#include "dd/dd.h"


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
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/
EXTERN void Import_init ARGS((void));
EXTERN void Import_init_cmd ARGS((void));

EXTERN void Import_reset ARGS((void));
EXTERN void Import_quit ARGS((void));

EXTERN void Import_do ARGS((FILE* file, BddFsm_ptr fsm));

#endif /* __IMPORT_H__ */
