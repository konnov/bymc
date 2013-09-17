/**CFile*****************************************************************

  FileName    [bymcPkg.c]

  PackageName [bymc]

  Synopsis    []

  Description []

  SeeAlso     [bymc.h]

  Author      [Igor konnov]

  Copyright   [ ]

******************************************************************************/

#if HAVE_CONFIG_H
# include "nusmv-config.h"
#endif 

#include "bymc.h"
#include "bymcInt.h"

#include "opt/opt.h"

#include <stdarg.h>
#include <stdio.h>

static char rcsid[] UTIL_UNUSED = "$Id: bymcPkg.c,v 1.1.2.3 2008-12-02 15:20:09 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis           [Initializes the addon]

  Description        []

  SideEffects        []

  SeeAlso            []

******************************************************************************/
void Bymc_init(void)
{
  if (opt_verbose_level_gt(OptsHandler_get_instance(), 0)) {
    fprintf(nusmv_stderr, "Initializing the BYMC package... \n");
  }
  Bymc_init_cmd(); 
}


/**Function********************************************************************

  Synopsis           [Reinitializes the addon]

  Description        []

  SideEffects        []

  SeeAlso            []

******************************************************************************/
void Bymc_reset(void)
{
}


/**Function********************************************************************

  Synopsis           [Deinitializes the addon]

  Description        []

  SideEffects        []

  SeeAlso            []

******************************************************************************/
void Bymc_quit(void)
{
  if (opt_verbose_level_gt(OptsHandler_get_instance(), 0)) {
    fprintf(nusmv_stderr, "Quitting the BYMC package... \n");
  }
}


