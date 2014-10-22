/*
 * Mathsat compatibility layer.
 *
 * Here we implement only the minimal set of functions required for ByMC.
 *
 * Igor Konnov, 2014
 */

#include <stdio.h>

int mathsat_start() {
    printf("Starting MathSat\n");
    fflush(stdout);
}

int mathsat_stop() {
    printf("Stopping MathSat\n");
    fflush(stdout);
}

