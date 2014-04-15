#!/bin/bash
#
# Functions specific to verification with FASTer.
#
# We also use NuSMV to collect the local reachable states;
# then the set of reachable states is abstracted with a pycudd script.
#
# Igor Konnov, 2014

FAST=${FAST:-fast}
FAST_PLUGIN=${FAST_PLUGIN:-lash-msdf}
NUSMV=${NUSMV:-nusmv}
ANALYSIS_OUT="analysis.out"
NUSMV_OUT="nusmv.out"

if [ -x "/usr/bin/time" ]; then 
    TIME="/usr/bin/time" # GNU time that shows memory usage
elif [ -x "$HOME/bin/time" ]; then 
    TIME="$HOME/bin/time"    # smth. compiled by the user
else
    TIME="time"          # shell time, almost useless
fi

function mc_compile_first {
    BYMC_FLAGS="--target nusmv --chain fast"
    echo ${TOOL} ${BYMC_FLAGS} -a ${PROG}
    tee_or_die "${ANALYSIS_OUT}" "bymc failed" \
        ${TIME} ${TOOL} ${BYMC_FLAGS} -a ${PROG}
}

# XXX: partially copied from mod-analysis, refactor
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
    tee_or_die "${NUSMV_OUT}" "nusmv failed" \
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

    # run again and produce process skeletons
    mc_compile_first

    # run fast
    echo $TIME ${NUSMV} $ARGS -source "${SCRIPT}" "${SRC}"
    tee_or_die "${MC_OUT}" "fast failed" \
        $TIME ${FAST} $ARGS --plugin=$FAST_PLUGIN -t model.fst

    # the exit code of grep is the return code
    if grep -q "specification is satisfied" ${MC_OUT}; then
        echo ""
        echo "Specification holds true." >>$MC_OUT
        echo ""
        true
    elif grep -q "specification is violated" ${MC_OUT}; then
        echo ""
        echo "Specification is violated." >>$MC_OUT
        echo ""
        false
    else
        false
    fi
}

function mc_refine {
    echo "error" >refinement.out
}

function mc_collect_stat {
    time_stat=`grep maxresident $MC_OUT | tail -n 1 | perl -n -e 'if (/(.*)user (.*)system (.*)elapsed.*avgdata\D*(\d+)maxresident.*/) { print "$1 $2 $3 $4\n" }'`
    fast_user=`echo $time_stat | cut -d ' ' -f 1`
    fast_sys=`echo $time_stat | cut -d ' ' -f 2`
    fast_elapsed=`echo $time_stat | cut -d ' ' -f 3`
    fast_maxres=`echo $time_stat | cut -d ' ' -f 4`
    
    # TODO: FINISH
    if grep -q "out of memory" ${MC_OUT}; then
        res="OOM"
    elif grep -q "terminated by signal 9" ${MC_OUT}; then
        res="TIMEOUT"
    elif grep -q "specification is satisfied" ${MC_OUT}; then
        res="SAT"
    elif grep -q "specification is violated" ${MC_OUT}; then
        res="UNSAT"
    elif grep -q "Abort" ${MC_OUT} || grep -q "syntax error" ${MC_OUT}; then
        res="ABORT"
    else
        res="MAYBE"
    fi

    echo "10:Result=$res|11:technique=fast|31:fast-plugin=$FAST_PLUGIN|32:fast-usersec=$fast_user|33:fast-syssec=$fast_sys|34:fast-elapsedsec=$fast_elapsed|35:fast-maxreskb=$fast_maxres"
}

