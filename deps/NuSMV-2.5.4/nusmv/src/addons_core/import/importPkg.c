/**CFile*****************************************************************

  FileName    [importPkg.c]

  PackageName [import]

  Synopsis    []

  Description []

  SeeAlso     [import.h]

  Author      [Igor konnov]

  Copyright   [ ]

******************************************************************************/

#if HAVE_CONFIG_H
# include "nusmv-config.h"
#endif 

#include "import.h"
#include "importInt.h"

#include "opt/opt.h"

#include <stdarg.h>
#include <stdio.h>

static char rcsid[] UTIL_UNUSED = "$Id: importPkg.c,v 1.1.2.3 2008-12-02 15:20:09 nusmv Exp $";

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
void Import_init(void)
{
  if (opt_verbose_level_gt(OptsHandler_get_instance(), 0)) {
    fprintf(nusmv_stderr, "Initializing the Import package... \n");
  }
  Import_init_cmd(); 
}


/**Function********************************************************************

  Synopsis           [Reinitializes the addon]

  Description        []

  SideEffects        []

  SeeAlso            []

******************************************************************************/
void Import_reset(void)
{
}


/**Function********************************************************************

  Synopsis           [Deinitializes the addon]

  Description        []

  SideEffects        []

  SeeAlso            []

******************************************************************************/
void Import_quit(void)
{
  if (opt_verbose_level_gt(OptsHandler_get_instance(), 0)) {
    fprintf(nusmv_stderr, "Quitting the Import package... \n");
  }
}


