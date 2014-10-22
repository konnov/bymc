/*
 * Mathsat compatibility layer.
 *
 * Here we implement only the minimal set of functions required for ByMC.
 *
 * Igor Konnov, 2014
 */

#include <stdio.h>
#include <stdlib.h>

#include <mathsat.h>

/* the maximum number of solvers */
#define MAX_ENVS 10000
static int n_envs = 0;
static msat_env* ap_envs[MAX_ENVS];

int mathsat_create() {
    msat_config cfg;
    msat_env* env;
    int env_no = n_envs;

    printf("starting mathsat %d\n", n_envs); fflush(stdout);
    if (n_envs >= MAX_ENVS) {
        fprintf(stderr, "Too many mathsat instances");
        return -1;
    }

    cfg = msat_create_config();
    msat_set_option(cfg, "model_generation", "true");
    msat_set_option(cfg, "unsat_core_generation", "1");
    if ((env = malloc(sizeof(msat_env))) == NULL) {
        fprintf(stderr, "Error allocating memory for mathsat environment");
        return -1;
    }
    *env = msat_create_env(cfg);
    ap_envs[env_no] = env; ++n_envs;
    msat_destroy_config(cfg);
    return env_no;
}

void mathsat_destroy(int env_no) {
    if (env_no <= n_envs || env_no < 0) {
        fprintf(stderr, "destroying non-existent mathsat %d\n", env_no);
        return;
    }
    printf("destroying mathsat %d\n", env_no); fflush(stdout);

    if (ap_envs[env_no] != NULL) {
        msat_destroy_env(*ap_envs[env_no]);
        free(ap_envs[env_no]);
        ap_envs[env_no] = NULL;
    }
    if (env_no + 1 == n_envs)
        --n_envs;
}

