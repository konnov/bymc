#!/bin/bash
#
# Run the abstraction refinement loop.
#
# Igor Konnov, 2012-2013

if [ "$#" -lt 2 ]; then
    echo "Not enough arguments"
    echo ""
    echo "Use: cegar promela_system property"
    exit 1
fi

ORIG_DIR=`pwd`

trap "cd $ORIG_DIR; kill 0" SIGHUP SIGINT SIGTERM
set -e # fail on first error
export CAMLRUNPARAM="b"

BYMC_HOME=`dirname $0`
BYMC_HOME=`cd $BYMC_HOME/..; pwd`
PROG=`"$BYMC_HOME"/script/realpath.py "$1"`  #instead of: `readlink -f $1`
PROP=$2
PLUGIN_DIR=`cd $BYMC_HOME/../plugins; pwd`
CEX="cex.trace"
MC_OUT="mc.out"
# the experiment number: if not set, then use the number of seconds since 1970
exp_no=${EXP_NO:-`date -u '+%s'`}
# hash the arguments to identify the experiment

cmd=""
step="0"
rand=""
out=""

START_TIME=0
INTERACTIVE=0

# an improved version of tee
function tee_or_die {
    FILE=$1
    MSG=$2
    shift 2
    echo "$@"
    {
        set -o pipefail
        $@ 2>&1 | tee $FILE
        RET=${PIPESTATUS}
        if [ "$RET" -ne "0" ]; then
            echo "$MSG" 1>&2
            exit $RET
        fi
    }
}

function die {
    echo "$1" 1>&2
    cd $ORIG_DIR
    exit 1
}

function to_verdict() {
    if [ "$out" == "" ]; then
        out="|00:exitcode=abort|01:valid=maybe|02:spurious=maybe|09:exp=$exp_no"
    fi

    END_TIME=$(date +%s)
    DIFF_TIME=$(($END_TIME-$START_TIME))

    stat=$(mc_collect_stat)
    common="03:refinements=$step|04:sys=`basename $PROG .pml`|05:spec=`basename $PROP .never`|06:total-sec=$DIFF_TIME|$stat"
    # the local verdict is useful when merging MPI results
    echo "$out|$common|$mc_stat" >>my-verdict.txt 
    cd $ORIG_DIR
    echo "$out|$common|$mc_stat" >>verdict.txt
}

trap "to_verdict" ERR EXIT

# interpret the functions specific to model checker
if [ "${TARGET_MC}" == "spin" ]; then
    . "${BYMC_HOME}/script/mod-verify-spin.sh"
elif [ "${TARGET_MC}" == "nusmv-bmc" ]; then
    . "${BYMC_HOME}/script/mod-verify-nusmv-bmc.sh"
elif [ "${TARGET_MC}" == "nusmv-bdd" ]; then
    . "${BYMC_HOME}/script/mod-verify-nusmv-bdd.sh"
elif [ "${TARGET_MC}" == "analysis" ]; then
    . "${BYMC_HOME}/script/mod-analyse.sh"
elif [ "${TARGET_MC}" == "post" ]; then
    . "${BYMC_HOME}/script/mod-post.sh"
elif [ "${TARGET_MC}" == "synt" ]; then
    . "${BYMC_HOME}/script/mod-synt.sh"
elif [ "${TARGET_MC}" == "fast" ]; then
    . "${BYMC_HOME}/script/mod-fast.sh"
else
    echo "Unsupported TARGET_MC='${TARGET_MC}'"
    exit 2
fi

cd $BYMC_HOME
if [ -d "src" ]; then
    # source distribution
    if [ "x$DEBUG" == "x" ]; then
        if [ -x "$BYMC_HOME/bymc.native" ]; then
            echo "Using the existing binary..."
        else
            make || (cd $ORIG_DIR; exit 1)
            echo "No binary found, compiling..."
        fi
        TOOL="$BYMC_HOME/bymc.native --plugin-dir ${PLUGIN_DIR} ${BYMC_FLAGS} "
    else
        # compile the latest version
        echo "Compiling bytecode..."
        BYTE="1" make || (cd $ORIG_DIR; exit 1)
        TOOL="ocamldebug $BYMC_HOME/bymc.byte --plugin-dir ${PLUGIN_DIR} "
    fi
else
    # binary distribution
    TOOL="$BYMC_HOME/bymc.native ${BYMC_FLAGS} "
fi
cd $ORIG_DIR

mkdir -p "$ORIG_DIR/x"
work_dir_template="$ORIG_DIR/x/`basename $PROG .pml`-$PROP-exp${exp_no}-`date \"+%y%m%d-%H%M\"`.XXXXXX"
work_dir=`mktemp -d $work_dir_template`
cd "$work_dir"
echo "Changed directory to $work_dir"

echo "" >$MC_OUT # create an empty output

START_TIME=$(date +%s)

if [ "$CONTINUE" == "" ]; then
    # first run: no refinement, generate the initial abstraction
    mc_compile_first
fi

rm -rf ${MC_OUT} ${CEX} refinement.out

while [ "$cmd" != "q" ]; do
    code=0
    mc_verify_spec || code=$?

    if [ "$code" == "0" ]; then
        echo "The property is verified in $step refinement steps"
        out="|00:exitcode=ok|01:valid=yes|02:spurious=no|09:exp=$exp_no"
        cmd="q"
    else
        mc_refine
        
        if grep "trace-no-refinement" refinement.out; then
            if [ "$INTERACTIVE" != "0" ]; then
                echo "Enter to try another trace, q<Enter> to exit"
                rand="-DT_RAND"
                read cmd
            else
                cmd="q"
            fi
        elif grep "error" refinement.out \
                || grep "trace-concrete-example" refinement.out; then
            echo "It took $step refinement steps"
            out="|00:exitcode=ok|01:valid=no|02:spurious=no|09:exp=$exp_no"
            cmd="q"
        elif grep "trace-refined" refinement.out; then
            step=$((step+1))
            echo "Refinement step #${step}."
            if [ "$DEBUG" != "" -o "$ASK" != "" ]; then
                echo "Enter to continue, q<Enter> to exit"
                read cmd
            fi
        else
            echo "Unknown refinement status. Aborted."
            cmd="q"
        fi
    fi
done

# here to_verdict fires

