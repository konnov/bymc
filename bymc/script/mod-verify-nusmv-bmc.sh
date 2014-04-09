#!/bin/bash
#
# Function specific to nusmv
#
# Igor Konnov, 2013

DEPTH=${DEPTH:-10} # parse options?

. $BYMC_HOME/script/mod-verify-nusmv-common.sh

function mc_compile_first {
    common_mc_compile_first
}

function mc_verify_spec {
    SCRIPT="script.nusmv"
    echo "set on_failure_script_quits" >$SCRIPT
    echo "go_bmc" >>$SCRIPT
    echo "time" >>$SCRIPT
    if grep -q "INVARSPEC NAME ${PROP}" "${SRC}"; then
        echo "check_invar_bmc -k $DEPTH -a een-sorensson -P ${PROP}" \
            >>${SCRIPT}
    else
        if [ "$COMPLETENESS" != "1" ]; then CF=""; else CF="-c"; fi
        if [ "$NO_UNROLLING" != "1" ]; then VU=""; else VU="-N"; fi
        if [ "$ONE_SHOT" != "1" ]; then
            echo "check_ltlspec_sbmc_inc $CF $VU -k $DEPTH -P ${PROP}" >>${SCRIPT}
        else
            echo "check_ltlspec_bmc_onepb -k $DEPTH -P ${PROP}" >>${SCRIPT}
        fi
    fi
    echo "time" >>$SCRIPT
    echo "show_traces -v -o ${CEX}" >>${SCRIPT}
    echo "quit" >>${SCRIPT}

    rm -f ${CEX}
    tee_or_die "$MC_OUT" "nusmv failed"\
        $TIME ${NUSMV} -df -v $NUSMV_VERBOSE -source "${SCRIPT}" "${SRC}"
    # the exit code of grep is the return code
    if [ '!' -f ${CEX} ]; then
        echo ""
        echo "No counterexample found with bounded model checking."
        echo "WARNING: To guarantee completeness, make sure that DEPTH is set properly"
        echo "as per completeness threshold"
        echo ""
        true
    else
        echo "Specification is violated." >>$MC_OUT
        false
    fi
}

function mc_refine {
    common_mc_refine
}

function mc_collect_stat {
    res=`common_mc_collect_stat | sed 's/10:Result=SAT/10:Result=BSAT/'`
    length=`grep "no counterexample found with bound" $MC_OUT | tail -n 1 \
        | sed 's/.*bound *\([0-9]*\)/\1/'`
    last=`grep 'Creating the formula specific k-dependent constraints' $MC_OUT \
        | perl -n -e 'if (/for k=(\d+)/) { print "$1\n" }' \
        | tail -n 2 | head -n 1`
    echo "$res|11:technique=nusmv-bmc|21:bmc-len=$length|22:bmc-last-len=$last"
}

