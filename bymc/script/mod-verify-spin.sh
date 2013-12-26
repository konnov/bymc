#!/bin/bash
#
# Function specific to spin
#
# Igor Konnov, 2012-2013

SPIN=${SPIN:-spin}
LTL2BA="$BYMC_HOME/../deps/ltl2ba-1.1/ltl2ba"
BYMC_FLAGS="--target spin"

if [ ! -x "$LTL2BA" ]; then
    echo "WARNING: $LTL2BA is not found. Please go to `dirname $LTL2BA` and run make."
    echo "WARNING: using 'spin -f' instead of ltl2ba. Performance may degrade."
    echo "********************************************************************"
    LTL2BA="$SPIN"
fi

function mc_compile_first {
    ${TOOL} ${BYMC_FLAGS} -a ${PROG} \
        || die "Failure: ${TOOL} -a ${PROG}"
}

function mc_verify_spec {
    echo "Converting the spec: !`head ${PROP}.ltl`..."
    ${LTL2BA} -f "!`head ${PROP}.ltl`" >${PROP}.never \
        || die "`cat ${PROP}.never`"
    echo "Generating pan..."
    set -x # echo on
    ${SPIN} -a -N ${PROP}.never abs-counter.prm || die "spin failed"
    gcc ${rand} ${PANCC_FLAGS} -o ./pan pan.c 
    set +x # echo off
    tee_or_die "${MC_OUT}" "pan failed" ./pan ${PAN_FLAGS} -a 2>&1

    # the status code of spin is the return value
    egrep -q "errors: +0" ${MC_OUT}
}

function mc_refine {
    ./pan -S | grep -v MSC | egrep '(^S\{|^X\{|START OF CYCLE)' > ${CEX} \
    && tee_or_die "refinement.out" "refinement error" ${TOOL} -t ${CEX} 2>&1

    echo -e "The trace in the ABSTRACT system (produced by spin):\n"
    echo -n "     0  "; head -n 1 ${CEX} # start with 0
    tail -n '+2' ${CEX} | ${BYMC_HOME}/script/nl.py -n 30
    echo ""
}

function mc_collect_stat {
    mc_stat=`$BYMC_HOME/script/parse-spin-out.py $MC_OUT`
    mc_stat="$mc_stat|technique=spin"
}

