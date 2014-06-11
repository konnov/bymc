#!/bin/bash
#
# Functions specific to nusmv using bdds
#
# Igor Konnov, 2013

. $BYMC_HOME/script/mod-verify-nusmv-common.sh

function mc_compile_first {
    common_mc_compile_first
}

function mc_verify_spec {
    if [ "$NO_JUSTICE" != "0" ]; then
        perl -pi -e 's/JUSTICE /-- JUSTICE/g' main-ssa.smv
    fi

    SCRIPT="script.nusmv"
    echo "set on_failure_script_quits" >$SCRIPT
    if [ "$SOURCE" != "" ]; then
        cat <"$SOURCE" >>$SCRIPT
    fi

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
    if [ "$REACH_REL" == "1" ]; then
        ARGS=""
    else
        ARGS="-df"
    fi
    if [ "$MONO" == "1" ]; then
        ARGS="$ARGS -mono"
    else
        ARGS="$ARGS"
    fi

    echo $TIME ${NUSMV} $ARGS -v $NUSMV_VERBOSE -source "${SCRIPT}" "${SRC}"
    tee_or_die "${MC_OUT}" "nusmv failed" \
        $TIME ${NUSMV} $ARGS -v $NUSMV_VERBOSE -source "${SCRIPT}" "${SRC}"

    # the exit code of grep is the return code
    if grep -q "is true" ${MC_OUT}; then
        echo ""
        echo "Specification holds true." >>$MC_OUT
        echo ""
        true
    elif grep -q "is false" ${MC_OUT}; then
        echo ""
        echo "Specification is violated." >>$MC_OUT
        echo ""
        false
    else
        false
    fi
}

function mc_refine {
    common_mc_refine
}

function mc_collect_stat {
    res=$(common_mc_collect_stat)
    echo "$res|11:technique=nusmv-bdd"
}

