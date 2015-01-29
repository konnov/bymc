#!/bin/bash
#
# Functions specific to partial order schedule tree
#
# Igor Konnov, 2014-2015

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

    stat=`perl <$POST_OUT -e '
while (<>) {
    if (/(.*)user (.*)system (.*)elapsed.*avgdata\D*(\d+)maxresident.*/) {
        $b_user = $1; $b_sys = $2; $b_elapsed = $3; $b_maxres = $4;
    }
    if (/PIA domain size: (\d+)/) { $dom_size = $1; }
    if (/.*the bound for.*is (\d+) =.*/) { $bound = $1; }
    if (/.*the mild bound for.*is (\d+).*/) { $mbound = $1; }
    if (/.*the counter abstraction bound for.*is (\d+).*/) { $cabound = $1; }
    if (/.*the mild counter abstraction bound for.*is (\d+).*/) { $mcabound = $1; }
    if (/.*the mild counter abstraction bound for.*is (\d+).*/) { $mcabound = $1; }
    if (/.*?(\d+) unlocking milestones/) { $unlocking = $1; }
    if (/.*?(\d+) locking milestones/) { $locking = $1; }
    if (/.*found (\d+) locations.*/) { $nlocs = $1; }
    if (/.*found (\d+) rules*/) { $nrules = $1; }
    if (/.*?(\d+) schemas to inspect*/) { $nschemas = $1; }
    if (/npaths = (\d+), min length = (\d+), max length = (\d+), avg length = (\d+)/) {
        $npaths = $1; $minlen = $2; $maxlen = $3; $avglen = $4;
    }
    if (/found (\d+) non-trivial SCCs/) { $nsccs = $1; }
}

print "40:post-usersec=${b_user}|41:post-syssec=${b_sys}\
|42:post-elapsedsec=${b_elapsed}|43:post-maxreskb=${b_maxres}\
|45:post-bound=${bound}|46:post-unlocking=${unlocking}\
|47:post-locking=${locking}|48:post-nlocs=${nlocs}\
|49:post-nrules=${nrules}\
|50:post-cabound=${cabound}|51:post-mild-cabound=${mcabound}\
|52:post-mild-bound=${mbound}|52:post-nschemas=${nschemas}\
|53:post-minlen=${minlen}|54:post-maxlen=${maxlen}\
|55:post-avglen=${avglen}|56:post-nsccs=${nsccs}\
|59:post-domsize=${dom_size}\n"
'`

    echo "10:Result=$res|$stat"
}

