#!/bin/bash
#
# Function specific to nusmv
#
# Igor Konnov, 2013

DEPTH=${DEPTH:-10} # parse options?

. $BYMC_HOME/script/mod-verify-nusmv-common.sh

if [ "$PLINGELING" -ne "0" ]; then
    CUSTOM_SAT=${LINGELING_TOOL:-plingeling}
    CUSTOM_SAT="$LINGELING_TOOL -t ${PLINGELING}"
fi

SAT_OUT="sat.out"

function comp_symb_skel {
    OF="$BYMC_FLAGS"
    BYMC_FLAGS="--target nusmv --chain skelSmv"
    echo ${TOOL} ${BYMC_FLAGS} -a ${PROG}
    tee_or_die "${ANALYSIS_OUT}" "bymc failed" \
        ${TIME} ${TOOL} ${BYMC_FLAGS} -a ${PROG}
    BYMC_FLAGS="$OF"
}

function abs_symb_skel {
    # XXX: copied from mod-analyse
    SCRIPT="skel-script.nusmv"
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
}

function mc_compile_first {
    if [ "$SKEL" != "1" ]; then
        common_mc_compile_first
    else
        CAMLRUNPARAM="b" $TIME ${TOOL} --target nusmv --chain skelSmv -a ${PROG} \
            || die "Failure: ${TOOL} -a ${PROG}"
    fi
}

function mc_verify_spec {
    if [ "$SKEL" == "1" ]; then
        SRC="main-sum.smv"
    fi

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
            echo "gen_ltlspec_sbmc -k $DEPTH -1 -P ${PROP}" >>${SCRIPT}
#            echo "check_ltlspec_bmc_onepb -k $DEPTH -P ${PROP}" >>${SCRIPT}
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
        if [ "$ONE_SHOT_LEN" -ne 0 ]; then
            CNF="oneshot${ONE_SHOT_LEN}"
            # lingeling solves one-shot problems much faster!
            echo "--------------------------------------"
            echo " Finished refinement for length $DEPTH."
            echo " Now running $CUSTOM_SAT for length $ONE_SHOT_LEN"
            echo "--------------------------------------"
            SCRIPT2="script-oneshot-custom-sat.smv"
            echo "set on_failure_script_quits" >$SCRIPT2
            echo "go_bmc" >>$SCRIPT2
            echo "time" >>$SCRIPT2
            echo "gen_ltlspec_sbmc -1 -k $ONE_SHOT_LEN -P ${PROP} -o ${CNF}" >>${SCRIPT2}
            # that consumes lots of memory
            #echo "gen_ltlspec_bmc_onepb -k $LINGELING -P ${PROP} -o ${CNF}" >>$SCRIPT2
            echo "time" >>$SCRIPT2
            echo "quit" >>$SCRIPT2
            tee_or_die "$MC_OUT" "nusmv failed"\
                $TIME ${NUSMV} -df -v $NUSMV_VERBOSE -source "$SCRIPT2" "${SRC}"
            set -o pipefail
            $TIME ${CUSTOM_SAT} 2>&1 "${CNF}.dimacs" | tee ${SAT_OUT}
            RET=${PIPESTATUS}

            if [ "$RET" -eq 20 ]; then
                echo "--------------------------------------"
                echo "No counterexample found with bounded model checking."
                echo "WARNING: To guarantee completeness, make sure"
                echo "         that -K (or --lingeling) is set properly"
                echo "         as per completeness threshold"
                true
            elif [ "$RET" -eq 10 ]; then
                false
            else
                die "lingeling reported UNKNOWN"
            fi
        else
            echo "--------------------------------------"
            echo "No counterexample found with bounded model checking."
            echo "WARNING: To guarantee completeness, make sure that --length is set properly"
            echo "as per completeness threshold"
            echo ""
            true
        fi
    else
        echo "Specification is violated." >>$MC_OUT
        false
    fi
}

function mc_refine {
    if [ "$SKEL" == "1" ]; then
        SRC="main-sum.smv"
        BYMC_FLAGS="--target nusmv --chain skelSmv"
    fi

    common_mc_refine
}

function mc_collect_stat {
    res=`common_mc_collect_stat | sed 's/10:Result=SAT/10:Result=BSAT/'`
    length=`grep "no counterexample found with bound" $MC_OUT | tail -n 1 \
        | sed 's/.*bound *\([0-9]*\)/\1/'`
    last=`grep 'Creating the formula specific k-dependent constraints' $MC_OUT \
        | perl -n -e 'if (/for k=(\d+)/) { print "$1\n" }' \
        | tail -n 2 | head -n 1`
    if [ "$ONE_SHOT_LEN" != "0" ]; then
        time_stat=`grep maxresident $SAT_OUT | tail -n 1 | perl -n -e 'if (/(.*)user (.*)system (.*)elapsed.*avgdata\D*(\d+)maxresident.*/) { print "$1 $2 $3 $4\n" }'`
        lingeling_elapsed=`echo $time_stat | cut -d ' ' -f 3`
        lingeling_maxres=`echo $time_stat | cut -d ' ' -f 4`
    fi
    echo "$res|11:technique=nusmv-bmc|21:bmc-len=$length|22:bmc-last-len=$last|25:lingeling-elapsedsec=$lingeling_elapsed|26:lingeling-maxreskb=$lingeling_maxres"
}

