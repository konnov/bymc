
#include "bymcInt.h"
#include "bymcImpl.h"

#include "enc/enc.h"
#include "enc/bdd/BddEnc.h"
#include "node/node.h"
#include "parser/symbols.h"
#include "opt/OptsHandler.h"
#include "prop/PropDb.h"
#include "prop/propPkg.h"
#include "fsm/bdd/BddFsm.h"
#include "trans/trans.h"
#include "trans/bdd/BddTrans.h"
#include "trans/bdd/Cluster.h"
#include "trans/bdd/ClusterList.h"

#include "dddmp.h"

int loadBdd(char* filename) {
    DdManager * dd;
    Cluster_ptr cluster;
    ClusterList_ptr clusters;
    NodeList_ptr out_vars;
    BddEnc_ptr enc;
    BddFsm_ptr bdd_fsm;
    BddTrans_ptr trans;
    BddVarSet_ptr state_cube, input_cube, next_state_cube;
    char* root_match_names[] = {"TRANS"};
    char** var_names = NULL;
    DdNode **pproots = NULL;
    int max_level, i = 0, ret = 0;

    /* parts of this code go from enc/bdd/BddEnc.c:BddEnc_get_var_ordering */
    enc = Enc_get_bdd_encoding();
    dd = BddEnc_get_dd_manager(enc);
    max_level = dd_get_size(dd);
    if ((var_names = malloc(sizeof(char*) * max_level)) == NULL) {
        fprintf(nusmv_stderr, "Cannot allocate memory for var_names\n");
        return 1;
    }

    var_names[0] = NULL; /* 0 is reserved for something */
    for (i = 1; i < max_level; ++i) {
        int index = dd_get_index_at_level(dd, i);
        node_ptr name = BddEnc_get_var_name_from_index(enc, index);
        if (name != Nil) {
            /* distinguish between current and NEXT variables */
            if (node_get_type(name) != NEXT)
                var_names[i] = sprint_node(name);
            else
                var_names[i] = sprint_node(name);

            fprintf(nusmv_stderr, "%d -> %s\n", i, var_names[i]);
        } else {
            var_names[i] = NULL;
        }
    }

    fprintf(nusmv_stderr, "Loading BDDs from %s...\n", filename);

    Dddmp_cuddBddArrayLoad(dd, DDDMP_ROOT_MATCHNAMES,
            root_match_names, DDDMP_VAR_MATCHNAMES, var_names, NULL, NULL,
            DDDMP_MODE_DEFAULT, filename, NULL, &pproots);
    fprintf(nusmv_stderr, "Done\n");

    fprintf(nusmv_stderr, "Overwriting the relations...\n");
    bdd_fsm = PropDb_master_get_bdd_fsm(PropPkg_get_prop_database());
    /* check BddTrans.h, it is actually much more complicated... */
    /*trans = BddFsm_get_trans(bdd_fsm);*/

    cluster = Cluster_create(dd);
    Cluster_set_trans(cluster, dd, pproots[0]);
    clusters = ClusterList_create(dd);
    ClusterList_append_cluster(clusters, cluster);

    state_cube = BddEnc_get_state_vars_cube(enc);
    input_cube = BddEnc_get_input_vars_cube(enc);                            
    next_state_cube = BddEnc_get_next_state_vars_cube(enc);

    trans = BddTrans_create(dd, clusters, (bdd_ptr) state_cube,
            (bdd_ptr) input_cube, (bdd_ptr) next_state_cube,
            TRANS_TYPE_MONOLITHIC,
            ClusterOptions_create(OptsHandler_get_instance()));

    bdd_fsm = BddFsm_create(BddFsm_get_bdd_encoding(bdd_fsm),
            BddFsm_get_init(bdd_fsm),
            BddFsm_get_state_constraints(bdd_fsm),
            BddFsm_get_input_constraints(bdd_fsm),
            trans,
            BddFsm_get_justice(bdd_fsm),
            BddFsm_get_compassion(bdd_fsm));

    PropDb_master_set_bdd_fsm(PropPkg_get_prop_database(), bdd_fsm);
clean:
    if (var_names != NULL) {
        for (i = 0; i < max_level; i++)
            FREE(var_names[i]);

        FREE(var_names);
    }

    return ret;
}

