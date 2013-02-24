
#include "importInt.h"
#include "importImpl.h"

#include "enc/enc.h"
#include "enc/bdd/BddEnc.h"
#include "node/node.h"

#include "dddmp.h"

int loadBdd(char* filename) {
    DdManager * dd_manager;
    NodeList_ptr out_vars;
    ListIter_ptr iter;
    char* root_match_names[] = {"TRANS"};
    char** var_names = NULL;
    DdNode **pproots = NULL;
    int var_cnt, i = 0, ret = 0;

    dd_manager = BddEnc_get_dd_manager(Enc_get_bdd_encoding());
    out_vars = BddEnc_get_var_ordering(Enc_get_bdd_encoding(), DUMP_BITS);
    var_cnt = NodeList_get_length(out_vars);
    if ((var_names = malloc(sizeof(char*) * var_cnt)) == NULL) {
        fprintf(nusmv_stderr, "Cannot allocate memory for var_names\n");
        return 1;
    }

    i = 0;
    iter = NodeList_get_first_iter(out_vars);
    while (!ListIter_is_end(iter)) {
        node_ptr name = NodeList_get_elem_at(out_vars, iter);
        var_names[i++] = util_strsav(sprint_node(name));
        iter = ListIter_get_next(iter);
    }
    NodeList_destroy(out_vars);
    fprintf(nusmv_stderr, "Loading BDDs from %s...\n", filename);

    Dddmp_cuddBddArrayLoad(dd_manager, DDDMP_ROOT_MATCHNAMES,
            root_match_names, DDDMP_VAR_MATCHNAMES, var_names, NULL, NULL,
            DDDMP_MODE_DEFAULT, filename, NULL, &pproots);
    fprintf(nusmv_stderr, "Done\n");

clean:
    if (var_names != NULL) {
        for (i = 0; i < var_cnt; i++)
            FREE(var_names[i]);

        FREE(var_names);
    }

    return ret;
}

