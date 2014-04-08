#!/bin/bash
#
# Functions specific to analysis
#
# Igor Konnov, 2014

NUSMV=${NUSMV:-nusmv}

function mc_compile_first {
    case "$PROP" in

    bound) BYMC_FLAGS="--target nusmv --chain bound" ;;
    *) echo "Unknown property to analyze: $PROP" ; exit 1 ;;
    esac
    echo ${TOOL} ${BYMC_FLAGS} -a ${PROG}
    ${TOOL} ${BYMC_FLAGS} -a ${PROG} || die "Failure: ${TOOL} -a ${PROG}"
}

function mc_verify_spec {
    SCRIPT="script.nusmv"
    echo "set on_failure_script_quits" >${SCRIPT}

    echo "go" >>${SCRIPT}
    echo "time" >>${SCRIPT}
    echo "compute_reachable" >>${SCRIPT}
    echo "time" >>${SCRIPT}
    echo "dump_fsm -r -o reach.dot" >>${SCRIPT}
    echo "quit" >>${SCRIPT}

    SRC=main-ssa-trans.smv # XXX: it works only if we have one process
    echo $TIME ${NUSMV} $ARGS -source "${SCRIPT}" "${SRC}"
    tee_or_die "${MC_OUT}" "nusmv failed" \
        $TIME ${NUSMV} $ARGS -source "${SCRIPT}" "${SRC}"

    D=${BYMC_HOME}/../bddc
    if [ ! -d "${D}" ]; then
        echo "Directory ${D} is not found"
        exit 1
    fi

    for f in vis-*.txt; do
        ${D}/with-pycudd ${D}/abs-reach.py reach.dot $f
        proc=`echo "$f" | sed 's/vis-\(.*\).txt/\1/'`
        cp flow.txt "local-tr-${proc}.txt"
    done

    mc_compile_first

    true
}

function mc_refine {
    echo ""
}

function mc_collect_stat {
    mc_stat="$mc_stat|11:technique=analysis"
}

