/**CFile*****************************************************************

  FileName    [importCmd.c]

  PackageName [import commands]

  Synopsis    []

  Description []

  SeeAlso     [import.h]

  Author      [Igor Konnov]

******************************************************************************/


#if HAVE_CONFIG_H
# include "nusmv-config.h"
#endif 

#include "import.h"
#include "importInt.h"

#include "opt/opt.h"
#include "cmd/cmd.h"
#include "enc/enc.h"
#include "prop/propPkg.h"
#include "utils/NodeList.h"
#include "utils/utils.h"
#include "parser/symbols.h"
#include "parser/parser.h"


static char rcsid[] UTIL_UNUSED = "$Id: importCmd.c,v 1.1.2.12 2010-02-02 10:09:32 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
static int UsageImportDo ARGS((void));


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

int CommandImportDo(int argc, char **argv);

/**Function********************************************************************

  Synopsis           [Initializes the commands provided by this package]

  Description        []

  SideEffects        []

******************************************************************************/
void Import_init_cmd()
{
  Cmd_CommandAdd("import_do", CommandImportDo, 0, true);
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
int CommandImportDo(int argc, char **argv)
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
  return UsageImportDo();

 __import_do_fail:
  if (dd_fname != (char*) NULL) FREE(dd_fname);
  return 1;
}

static int UsageImportDo()
{
  fprintf(nusmv_stderr, "usage: import_do [-h] [-f <bdd-fname>]\n");
  fprintf(nusmv_stderr, "  -h \t\t Prints the command usage.\n");
  fprintf(nusmv_stderr, "  -f <fname>\t Read INIT and TRANS BDDs saved with dddmp.\n");

  return 1;
}
