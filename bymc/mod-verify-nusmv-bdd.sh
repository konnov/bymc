#!/bin/bash
#
# Functions specific to nusmv using bdds
#
# Igor Konnov, 2013

NUSMV=${NUSMV:-nusmv}
BYMC_FLAGS="--target nusmv"

SRC_REACH="main-ssa-reach.smv"
SRC="main-ssa.smv"
HIDDEN="main-ssa-hidden.txt"
TIME="/usr/bin/time"

function mc_compile_first {
    rm -f "$HIDDEN"
    echo "Generating initial abstraction..."
    CAMLRUNPARAM="b" ${TOOL} ${BYMC_FLAGS} -a ${PROG} \
        || report_and_quit "Failure: ${TOOL} -a ${PROG}"
    echo "[DONE]"
    echo "Checking reachability of the local states..."
    $TIME ${BYMC_HOME}/nusmv-find-reach "${NUSMV}" "${SRC_REACH}" "${HIDDEN}"
    echo "[DONE]"
    echo "Generating smaller abstraction..."
    CAMLRUNPARAM="b" $TIME ${TOOL} ${BYMC_FLAGS} -a ${PROG} \
        || report_and_quit "Failure: ${TOOL} -a ${PROG}"
    echo "[DONE]"
    echo ""
}

function mc_verify_spec {
    SCRIPT="script.nusmv"
    echo "set on_failure_script_quits" >$SCRIPT
    echo "go" >>$SCRIPT
    echo "time" >>$SCRIPT
    if grep -q "INVARSPEC NAME ${PROP}" "${SRC}"; then
        echo "check_invar -P ${PROP}" >>${SCRIPT}
    else
        echo "check_ltlspec -P ${PROP}" >>${SCRIPT}
    fi
    echo "time" >>$SCRIPT
    echo "show_traces -v -o ${CEX}" >>${SCRIPT}
    echo "quit" >>${SCRIPT}

    rm -f ${CEX}
    $TIME ${NUSMV} -df -v $NUSMV_VERBOSE -source "${SCRIPT}" "${SRC}" | tee "${MC_OUT}" \
        || report_and_quit "nusmv failed"
    # the exit code of grep is the return code
    if grep -q "is true" ${MC_OUT}; then
        echo ""
        echo "Specification holds true."
        echo ""
        true
    else
        false
    fi
}

function mc_refine {
    CAMLRUNPARAM="b" $TIME ${TOOL} -t ${CEX} ${PROG} 2>&1 | tee refinement.out
    echo ""
}

function mc_collect_stat {
    # TODO: collect the statistics
    mc_stat="|technique=nusmv-bdd"
}

