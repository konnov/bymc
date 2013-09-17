/**CHeaderFile*****************************************************************

  FileName    [bymc.h]

  PackageName [addons.bymc]

  Synopsis    [The header file of the <tt>bymc</tt> addon.]

  Description [The <tt>bymc</tt> implementation package]

  Author      [Igor Konnov]

******************************************************************************/

#ifndef __BYMC_H__
#define __BYMC_H__

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
EXTERN void Bymc_init ARGS((void));
EXTERN void Bymc_init_cmd ARGS((void));

EXTERN void Bymc_reset ARGS((void));
EXTERN void Bymc_quit ARGS((void));

EXTERN void Bymc_do ARGS((FILE* file, BddFsm_ptr fsm));

#endif /* __BYMC_H__ */
