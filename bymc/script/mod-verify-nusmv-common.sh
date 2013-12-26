#!/bin/bash
#
# Function specific to nusmv
#
# Igor Konnov, 2013

NUSMV=${NUSMV:-nusmv}
BYMC_FLAGS="--target nusmv"

SRC_REACH="main-ssa-reach.smv"
SRC="main-ssa.smv"
HIDDEN="main-ssa-hidden.txt"
TIME="/usr/bin/time"

function common_mc_compile_first {
    if [ "$NO_REACH" != "1" -a "$NO_INITIAL" != "1" ]; then
        rm -f "$HIDDEN"
        echo "GENERATING INITIAL ABSTRACTION..."
        CAMLRUNPARAM="b" $TIME ${TOOL} ${BYMC_FLAGS} -a ${PROG} \
            || die "Failure: ${TOOL} -a ${PROG}"
        echo "[DONE]"

        echo "CHECKING REACHABILITY OF THE LOCAL STATES..."
        $TIME ${BYMC_HOME}/nusmv-find-reach "${NUSMV}" "${SRC_REACH}" "${HIDDEN}"
        echo "[DONE]"
    else
        echo "SKIPPED REACHABILITY ANALYSIS..."
    fi
    if [ "$NO_INITIAL" != "1" ]; then
        echo "GENERATING SMALLER ABSTRACTION..."
        CAMLRUNPARAM="b" $TIME ${TOOL} ${BYMC_FLAGS} -a ${PROG} \
            || die "Failure: ${TOOL} -a ${PROG}"
        echo "[DONE]"
        echo ""
    else
        echo "SKIPPED INITIAL ABSTRACTION..."
    fi
}

function common_mc_refine {
    echo "common_mc_refine"
    tee_or_die refinement.out "refinement error" \
        $TIME ${TOOL} -t ${CEX} ${PROG} 2>&1
}

function common_mc_collect_stat () {
    if grep -q "Out of memory" ${MC_OUT}; then
        res="OOM"
    elif grep -q "terminated by signal 9" ${MC_OUT}; then
        res="TIMEOUT"
    elif grep -q "Specification holds true" ${MC_OUT}; then
        res="SUCCESS"
    elif grep -q "Specification is violated" ${MC_OUT}; then
        res="ERROR"
    else
        res="MAYBE"
    fi

    echo "10:Result=$res"
}

