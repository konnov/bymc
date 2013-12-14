#!/bin/bash
#
# Function specific to nusmv
#
# Igor Konnov, 2013

NUSMV=${NUSMV:-nusmv}
DEPTH=${DEPTH:-10} # parse options?
BYMC_FLAGS="--target nusmv"

SRC_REACH="main-ssa-reach.smv"
SRC="main-ssa.smv"
HIDDEN="main-ssa-hidden.txt"
TIME="/usr/bin/time"

function mc_compile_first {
    if [ "$NO_REACH" != "1" -a "$NO_INITIAL" != "1" ]; then
        rm -f "$HIDDEN"
        echo "GENERATING INITIAL ABSTRACTION..."
        CAMLRUNPARAM="b" ${TOOL} ${BYMC_FLAGS} -a ${PROG} \
            || report_and_quit "Failure: ${TOOL} -a ${PROG}"
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
            || report_and_quit "Failure: ${TOOL} -a ${PROG}"
        echo "[DONE]"
        echo ""
    else
        echo "SKIPPED INITIAL ABSTRACTION..."
    fi
}

function mc_verify_spec {
    SCRIPT="script.nusmv"
    echo "set on_failure_script_quits" >$SCRIPT
    echo "go_bmc" >>$SCRIPT
    if grep -q "INVARSPEC NAME ${PROP}" "${SRC}"; then
        echo "check_invar_bmc -k $DEPTH -a een-sorensson -P ${PROP}" \
            >>${SCRIPT}
    else
        if [ "$ONE_SHOT" != "1" ]; then
            echo "check_ltlspec_bmc_inc -k $DEPTH -P ${PROP}" >>${SCRIPT}
        else
            echo "check_ltlspec_bmc_onepb -k $DEPTH -P ${PROP}" >>${SCRIPT}
        fi
    fi
    echo "show_traces -v -o ${CEX}" >>${SCRIPT}
    echo "quit" >>${SCRIPT}

    rm -f ${CEX}
    $TIME ${NUSMV} -df -v $NUSMV_VERBOSE -source "${SCRIPT}" "${SRC}" | tee "${MC_OUT}" \
        || report_and_quit "nusmv failed"
    # the exit code of grep is the return code
    if [ '!' -f ${CEX} ]; then
        echo ""
        echo "No counterexample found with bounded model checking."
        echo "WARNING: To guarantee completeness, make sure that DEPTH is set properly"
        echo "as per completeness threshold"
        echo ""
        true
    else
        false
    fi
}

function mc_refine {
    CAMLRUNPARAM="b" ${TOOL} -t ${CEX} ${PROG} 2>&1 | tee refinement.out
    echo ""
}

function mc_collect_stat {
    # TODO: collect the statistics
    mc_stat="|technique=nusmv-bmc"
}

