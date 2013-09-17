/**CFile*****************************************************************

  FileName    [bymcCmd.c]

  PackageName [bymc commands]

  Synopsis    []

  Description []

  SeeAlso     [bymc.h]

  Author      [Igor Konnov]

******************************************************************************/


#if HAVE_CONFIG_H
# include "nusmv-config.h"
#endif 

#include "bymc.h"
#include "bymcInt.h"
#include "bymcImpl.h"

#include "opt/opt.h"
#include "cmd/cmd.h"
#include "enc/enc.h"
#include "prop/propPkg.h"
#include "utils/NodeList.h"
#include "utils/utils.h"
#include "parser/symbols.h"
#include "parser/parser.h"


static char rcsid[] UTIL_UNUSED = "$Id: bymcCmd.c,v 1.1.2.12 2010-02-02 10:09:32 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
static int UsageBymcReach ARGS((void));


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

int CommandBymcReach(int argc, char **argv);

/**Function********************************************************************

  Synopsis           [Initializes the commands provided by this package]

  Description        []

  SideEffects        []

******************************************************************************/
void Bymc_init_cmd()
{
  Cmd_CommandAdd("bymc-reach", CommandBymcReach, 0, true);
}


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/



/**Function********************************************************************

  Synopsis           []

  CommandName        []            

  CommandSynopsis    []  

  CommandArguments   []  

  CommandDescription []  

  SideEffects        []

******************************************************************************/
int CommandBymcReach(int argc, char **argv)
{
  int c = 0;
  const char* dd_fname = (char*) NULL;

  util_getopt_reset();
  while ((c = util_getopt(argc, argv, "hf:")) != EOF) {
    switch (c) {
    case 'h': goto __import_do_fail_help;
    case 'f': 
      if (dd_fname != (char*) NULL) { FREE(dd_fname); }
      dd_fname = util_strsav(util_optarg);
      break;
      
    default: goto __import_do_fail_help;
    }
  }

  if (argc != util_optind) goto __import_do_fail_help;

  /* preconditions */
  if (Compile_check_if_flat_model_was_built(nusmv_stderr, false) ||
      Compile_check_if_encoding_was_built(nusmv_stderr)) goto __import_do_fail;

  /* do the job */
  if (loadBdd(dd_fname))
      goto __import_do_fail;

  /* success here */
  if (dd_fname != (char*) NULL) FREE(dd_fname);
  return 0;

  /* failure handlers */
 __import_do_fail_help:
  if (dd_fname != (char*) NULL) FREE(dd_fname);
  return UsageBymcReach();

 __import_do_fail:
  if (dd_fname != (char*) NULL) FREE(dd_fname);
  return 1;
}

static int UsageBymcReach()
{
  fprintf(nusmv_stderr, "usage: bymc_reach [-h] [-f <bdd-fname>]\n");
  fprintf(nusmv_stderr, "  -h \t\t Prints the command usage.\n");
  fprintf(nusmv_stderr, "  -f <fname>\t Read INIT and TRANS BDDs saved with dddmp.\n");

  return 1;
}
