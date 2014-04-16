#!/bin/bash
#
# Functions specific to analysis
#
# Igor Konnov, 2014

NUSMV=${NUSMV:-nusmv}
ANALYSIS_OUT="analysis.out"

if [ -x "/usr/bin/time" ]; then 
    TIME="/usr/bin/time" # GNU time that shows memory usage
elif [ -x "$HOME/bin/time" ]; then 
    TIME="$HOME/bin/time"    # smth. compiled by the user
else
    TIME="time"          # shell time
fi

function mc_compile_first {
    case "$PROP" in
      bounds) BYMC_FLAGS="--target nusmv --chain bounds" ;;
      *) echo "Unknown property to analyze: $PROP" ; exit 1 ;;
    esac
    echo ${TOOL} ${BYMC_FLAGS} -a ${PROG}
    tee_or_die "${ANALYSIS_OUT}" "bymc failed" \
        ${TIME} ${TOOL} ${BYMC_FLAGS} -a ${PROG}
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

    # run again and compute the bounds this time
    mc_compile_first

    true
}

function mc_refine {
    echo ""
}

function mc_collect_stat {
    time_stat=`grep maxresident $MC_OUT | tail -n 1 | perl -n -e 'if (/(.*)user (.*)system (.*)elapsed.*avgdata\D*(\d+)maxresident.*/) { print "$1 $2 $3 $4\n" }'`
    smv_user=`echo $time_stat | cut -d ' ' -f 1`
    smv_sys=`echo $time_stat | cut -d ' ' -f 2`
    smv_elapsed=`echo $time_stat | cut -d ' ' -f 3`
    smv_maxres=`echo $time_stat | cut -d ' ' -f 4`
    time_stat=`grep maxresident $ANALYSIS_OUT | tail -n 1 | perl -n -e 'if (/(.*)user (.*)system (.*)elapsed.*avgdata\D*(\d+)maxresident.*/) { print "$1 $2 $3 $4\n" }'`
    b_user=`echo $time_stat | cut -d ' ' -f 1`
    b_sys=`echo $time_stat | cut -d ' ' -f 2`
    b_elapsed=`echo $time_stat | cut -d ' ' -f 3`
    b_maxres=`echo $time_stat | cut -d ' ' -f 4`
    bound=`grep "the bound for" $ANALYSIS_OUT | tail -n 1 \
        | perl -n -e 'if (/.*bound for.*is (\d+) =.*/) { print "$1\n" }'`
    cabound=`grep "the counter abstraction bound for" $ANALYSIS_OUT | tail -n 1 \
        | perl -n -e 'if (/.*bound for.*is (\d+) =.*/) { print "$1\n" }'`
    mcabound=`grep "the mild counter abstraction bound for" $ANALYSIS_OUT | tail -n 1 \
        | perl -n -e 'if (/.*bound for.*is (\d+).*/) { print "$1\n" }'`
    backward=`grep "backward unlocking" $ANALYSIS_OUT | tail -n 1 \
        | perl -n -e 'if (/.*(\d+) backward unlocking.*/) { print "$1\n" }'`
    forward=`grep "forward locking" $ANALYSIS_OUT | tail -n 1 \
        | perl -n -e 'if (/.*(\d+) forward locking.*/) { print "$1\n" }'`
    nlocs=`grep "locations" $ANALYSIS_OUT | tail -n 1 \
        | perl -n -e 'if (/.*there are (\d+) locations.*/) { print "$1\n" }'`
    nrules=`grep "rules" $ANALYSIS_OUT | tail -n 1 \
        | perl -n -e 'if (/.*there are (\d+) rules*/) { print "$1\n" }'`

    echo "10:Result=OK|11:technique=analysis|12:nusmv-usersec=$smv_user|13:nusmv-syssec=$smv_sys|14:nusmv-elapsedsec=$smv_elapsed|15:nusmv-maxreskb=$smv_maxres|20:analysis-usersec=$b_user|21:analysis-syssec=$b_sys|22:analysis-elapsedsec=$b_elapsed|23:analysis-maxreskb=$b_maxres|25:analysis-bound=$bound|26:analysis-backward=$backward|27:analysis-forward=$forward|28:analysis-nlocs=$nlocs|29:analysis-nrules=$nrules|30:analysis-cabound=$cabound|31:analysis-mild-cabound=$mcabound"
}

