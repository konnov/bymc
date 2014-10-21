/*
 * Mathsat compatibility layer.
 *
 * Here we implement only the minimal set of functions required for ByMC.
 *
 * Igor Konnov, 2014
 */

#include <stdio.h>

int start() {
    printf("Starting MathSat\n");
}

int stop() {
    printf("Stopping MathSat\n");
}

