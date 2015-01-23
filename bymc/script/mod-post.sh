#!/bin/bash
#
# Functions specific to partial order schedule tree
#
# Igor Konnov, 2014

NUSMV=${NUSMV:-nusmv}
POST_OUT="post.out"

if [ -x "/usr/bin/time" ]; then 
    TIME="/usr/bin/time" # GNU time that shows memory usage
elif [ -x "$HOME/bin/time" ]; then 
    TIME="$HOME/bin/time"    # smth. compiled by the user
else
    TIME="time"          # shell time
fi

function mc_compile_first {
    BYMC_FLAGS="--target none --chain post --spec $PROP"
    echo ${TOOL} ${BYMC_FLAGS} -a "${PROG}"
    tee_or_die "${POST_OUT}" "bymc failed" \
        ${TIME} ${TOOL} ${BYMC_FLAGS} -a ${PROG}
}

function mc_verify_spec {
    egrep -q "counterexample for .* found" ${POST_OUT}
    test "$?" -ne 0
}

function mc_refine {
    false
}

function mc_collect_stat {
    if egrep -q "counterexample for .* found" ${POST_OUT}; then
        res="ERROR"
    else
        res="SUCCESS"
    fi

    time_stat=`grep maxresident $POST_OUT | tail -n 1 | perl -n -e 'if (/(.*)user (.*)system (.*)elapsed.*avgdata\D*(\d+)maxresident.*/) { print "$1 $2 $3 $4\n" }'`
    b_user=`echo $time_stat | cut -d ' ' -f 1`
    b_sys=`echo $time_stat | cut -d ' ' -f 2`
    b_elapsed=`echo $time_stat | cut -d ' ' -f 3`
    b_maxres=`echo $time_stat | cut -d ' ' -f 4`
    bound=`grep "the bound for" $POST_OUT | tail -n 1 \
        | perl -n -e 'if (/.*bound for.*is (\d+) =.*/) { print "$1\n" }'`
    mbound=`grep "the mild bound for" $POST_OUT | tail -n 1 \
        | perl -n -e 'if (/.*bound for.*is (\d+).*/) { print "$1\n" }'`
    cabound=`grep "the counter abstraction bound for" $POST_OUT | tail -n 1 \
        | perl -n -e 'if (/.*bound for.*is (\d+) =.*/) { print "$1\n" }'`
    mcabound=`grep "the mild counter abstraction bound for" $POST_OUT | tail -n 1 \
        | perl -n -e 'if (/.*bound for.*is (\d+).*/) { print "$1\n" }'`
    unlocking=`grep "[0-9] unlocking milestones" $POST_OUT | tail -n 1 \
        | perl -n -e 'if (/.*(\d+) unlocking.*/) { print "$1\n" }'`
    locking=`egrep "[0-9] locking milestones" $POST_OUT | tail -n 1 \
        | perl -n -e 'if (/.*(\d+) locking.*/) { print "$1\n" }'`
    nlocs=`grep "locations" $POST_OUT | tail -n 1 \
        | perl -n -e 'if (/.*found (\d+) locations.*/) { print "$1\n" }'`
    nrules=`grep "rules" $POST_OUT | tail -n 1 \
        | perl -n -e 'if (/.*found (\d+) rules*/) { print "$1\n" }'`
    nschemas=`grep "schemas to inspect" $POST_OUT | tail -n 1 \
        | perl -n -e 'if (/\D*(\d+) schemas to inspect*/) { print "$1\n" }'`
    schema_stat=`grep "npaths =" $POST_OUT`
    npaths=`echo $schema_stat | perl -n -e 'if (/npaths = (\d+), min length = (\d+), max length = (\d+), avg length = (\d+)/) { print "$1\n" }'`
    minlen=`echo $schema_stat | perl -n -e 'if (/npaths = (\d+), min length = (\d+), max length = (\d+), avg length = (\d+)/) { print "$2\n" }'`
    maxlen=`echo $schema_stat | perl -n -e 'if (/npaths = (\d+), min length = (\d+), max length = (\d+), avg length = (\d+)/) { print "$3\n" }'`
    avglen=`echo $schema_stat | perl -n -e 'if (/npaths = (\d+), min length = (\d+), max length = (\d+), avg length = (\d+)/) { print "$4\n" }'`

    echo "10:Result=$res|11:technique=post|40:post-usersec=$b_user|41:post-syssec=$b_sys|42:post-elapsedsec=$b_elapsed|43:post-maxreskb=$b_maxres|45:post-bound=$bound|46:post-unlocking=$unlocking|47:post-locking=$locking|48:post-nlocs=$nlocs|49:post-nrules=$nrules|50:post-cabound=$cabound|51:post-mild-cabound=$mcabound|52:post-mild-bound=$mbound|52:post-nschemas=$nschemas|53:post-minlen=$minlen|54:post-maxlen=$maxlen|55:post-avglen=$avglen"
}

