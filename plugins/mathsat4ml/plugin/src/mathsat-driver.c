/*
 * Mathsat compatibility layer.
 *
 * Here we implement only the minimal set of functions required for ByMC.
 *
 * Igor Konnov, 2014
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <mathsat.h>

/* the maximum number of solvers */
#define MAX_ENVS 10000
static int n_envs = 0;
static msat_env* ap_envs[MAX_ENVS];

/* the temporary buffer */
#define BUF_SIZE 10000
static char buf[BUF_SIZE];

int mathsat_create() {
    msat_config cfg;
    msat_env* env;
    int env_no = n_envs;

    if (n_envs >= MAX_ENVS) {
        fprintf(stderr, "Too many mathsat instances");
        return -1;
    }
    printf("starting mathsat %d\n", n_envs); fflush(stdout);

    cfg = msat_create_config();
    msat_set_option(cfg, "model_generation", "true");
    msat_set_option(cfg, "unsat_core_generation", "1");
    if ((env = malloc(sizeof(msat_env))) == NULL) {
        fprintf(stderr, "Error allocating memory for mathsat environment");
        return -1;
    }
    *env = msat_create_env(cfg);
    ap_envs[env_no] = env;
    ++n_envs;
    msat_destroy_config(cfg);
    return env_no;
}

void mathsat_destroy(int env_no) {
    if (env_no >= n_envs || env_no < 0) {
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

void mathsat_declare_int(int env_no, const char* name) {
    msat_env env;
    if (env_no >= n_envs || env_no < 0) {
        fprintf(stderr, "Accessing non-existent environment %d >= %d\n",
                env_no, n_envs);
        abort();
    }
    env = *ap_envs[env_no]; 
    msat_declare_function(env, name, msat_get_integer_type(env));
    /* we do not the declaration any more, as the assertions are going
     * to be created from a string */
}

int mathsat_assert(int env_no, const char* expr_text) {
    msat_env env;
    msat_term res;
    if (env_no >= n_envs || env_no < 0) {
        fprintf(stderr, "Accessing non-existent environment %d >= %d\n",
                env_no, n_envs);
        abort();
    }
    env = *ap_envs[env_no]; 
    res = msat_from_string(env, expr_text);
    if (MSAT_ERROR_TERM(res))
        return -1;
    else {
        msat_assert_formula(env, res);
        return msat_term_id(res);
    }
}

int mathsat_solve(int env_no) {
    msat_env env;
    msat_result res;
    if (env_no >= n_envs || env_no < 0) {
        fprintf(stderr, "Accessing non-existent environment %d >= %d\n",
                env_no, n_envs);
        abort();
    }
    env = *ap_envs[env_no]; 
    res = msat_solve(env);
    switch (res) {
        case MSAT_SAT:      return 1;
        case MSAT_UNKNOWN:  return -1;
        case MSAT_UNSAT:    return 0;
        default:            return -1;
    }
}

void mathsat_push(int env_no) {
    msat_env env;
    if (env_no >= n_envs || env_no < 0) {
        fprintf(stderr, "Accessing non-existent environment %d >= %d\n",
                env_no, n_envs);
        abort();
    }
    env = *ap_envs[env_no]; 
    if (msat_push_backtrack_point(env) != 0) {
        fprintf(stderr, "error pushing a backtrack point");
        abort();
    }
}

void mathsat_pop(int env_no) {
    msat_env env;
    if (env_no >= n_envs || env_no < 0) {
        fprintf(stderr, "Accessing non-existent environment %d >= %d\n",
                env_no, n_envs);
        abort();
    }
    env = *ap_envs[env_no]; 
    if (msat_pop_backtrack_point(env) != 0) {
        fprintf(stderr, "error popping a backtrack point");
        abort();
    }
}

const char* mathsat_get_model_value(int env_no, const char* term_text) {
    msat_env env;
    msat_term term;
    char* s;
    size_t len;
    if (env_no >= n_envs || env_no < 0) {
        fprintf(stderr, "Accessing non-existent environment %d >= %d\n",
                env_no, n_envs);
        abort();
    }
    env = *ap_envs[env_no]; 
    term = msat_from_string(env, term_text);
    if (MSAT_ERROR_TERM(term)) {
        fprintf(stderr, "Malformed term: %s\n", term_text);
        abort();
    }

    term = msat_get_model_value(env, term);
    s = msat_to_smtlib2_term(env, term);
    if (s == NULL) {
        fprintf(stderr, "msat_get_model_value returned NULL on: %s\n",
                term_text);
        abort();
    }

    len = 1 + strlen(s);
    if (len > BUF_SIZE) {
        fprintf(stderr, "The value is %zd chars long, the maximum is %d\n",
                len, BUF_SIZE);
        abort();
    }
    strncpy(buf, s, (len < BUF_SIZE ? len : BUF_SIZE));
    msat_free(s);
    return buf;
}

