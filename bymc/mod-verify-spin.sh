#!/bin/bash
#
# Function specific to spin
#
# Igor Konnov, 2012-2013

SPIN=${SPIN:-spin}
LTL2BA="$BYMC_HOME/../deps/ltl2ba-1.1/ltl2ba"
#PANCC_FLAGS=${PANCC_FLAGS:-"-DVECTORSZ=2048 -DCOLLAPSE -DSC -DNOREDUCE"}
PANCC_FLAGS=${PANCC_FLAGS:-"-DCOLLAPSE -DNOREDUCE"}
PAN_FLAGS=${PAN_FLAGS:-"-m100000"}
BYMC_FLAGS="--target spin"

if [ ! -x "$LTL2BA" ]; then
    echo "WARNING: $LTL2BA is not found. Please go to `dirname $LTL2BA` and run make."
    echo "WARNING: using 'spin -f' instead of ltl2ba. Performance may degrade."
    echo "********************************************************************"
    LTL2BA="$SPIN"
fi

function mc_compile_first {
    CAMLRUNPARAM="b" ${TOOL} ${BYMC_FLAGS} -a ${PROG} \
        || report_and_quit "Failure: ${TOOL} -a ${PROG}"
}

function mc_verify_spec {
    echo "Converting the spec: !`head ${PROP}.ltl`..."
    ${LTL2BA} -f "!`head ${PROP}.ltl`" >${PROP}.never \
        || (report_and_quit "`cat ${PROP}.never`")
    echo "Generating pan..."
    set -x # echo on
    ${SPIN} -a -N ${PROP}.never abs-counter.prm || report_and_quit "spin failed"
    (gcc ${rand} ${PANCC_FLAGS} -o ./pan pan.c \
        && ./pan ${PAN_FLAGS} -a 2>&1 | tee ${MC_OUT}) \
        || report_and_quit "pan failed"
    set +x # echo off
}

function mc_refine {
    ./pan -S | grep -v MSC | egrep '(^S\{|^X\{|START OF CYCLE)' > ${CEX} \
    && CAMLRUNPARAM="b" ${TOOL} -t ${CEX} ${PROG} 2>&1 \
        | tee refinement.out

    echo -e "The trace in the ABSTRACT system (produced by spin):\n"
    echo -n "     0  "; head -n 1 ${CEX} # start with 0
    tail -n '+2' ${CEX} | ${BYMC_HOME}/script/nl.py -n 30
    echo ""
}

function mc_collect_stat {
    mc_stat=`$BYMC_HOME/script/parse-spin-out.py $MC_OUT`
}

