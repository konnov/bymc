#!/bin/bash
#
# Functions specific to synthesis
#
# Igor Konnov, 2016

SYNT_OUT="synt"

if [ -x "/usr/bin/time" ]; then 
    TIME="/usr/bin/time" # GNU time that shows memory usage
elif [ -x "$HOME/bin/time" ]; then 
    TIME="$HOME/bin/time"    # smth. compiled by the user
else
    TIME="time"          # shell time
fi

function mc_compile_first {
    true
}

function mc_verify_spec {
    BYMC_FLAGS="--target none --chain synt --spec $PROP"
    echo ${TOOL} ${BYMC_FLAGS} -a "${PROG}"
    tee_or_die "${SYNT_OUT}" "bymc failed" \
        ${TIME} ${TOOL} ${BYMC_FLAGS} -a ${PROG}
    egrep -q "counterexample for .* found" ${SYNT_OUT}
    test "$?" -ne 0
}

function mc_refine {
    if [ -f "cex-fixme.trx" ]; then
        echo "error" >refinement.out
        tee_or_die "refinement.out" "refinement error" ${TOOL} -t cex-fixme.trx 2>&1
    fi
}

function mc_collect_stat {
    if grep -q "Out of memory" ${SYNT_OUT}; then
        res="OOM"
    elif grep -q "terminated by signal 9" ${SYNT_OUT}; then
        res="TIMEOUT"
    elif grep -q "terminated by signal" ${SYNT_OUT}; then
        res="ERR"
    elif grep -q "unknown result" ${SYNT_OUT}; then
        res="ERR"
    elif egrep -q "counterexample for .* found" ${SYNT_OUT}; then
        res="UNSAT"
    else
        res="SAT"
    fi

    stat=`perl <$SYNT_OUT -e '
while (<>) {
    if (/(.*)user (.*)system (.*)elapsed.*avgdata\D*(\d+)maxresident.*/) {
        $b_user = $1; $b_sys = $2; $b_elapsed = $3; $b_maxres = $4;
    }
    if (/.*?(\d+) unlocking milestones/) { $unlocking = $1; }
    if (/.*?(\d+) locking milestones/) { $locking = $1; }
    if (/.*found (\d+) locations.*/) { $nlocs = $1; }
    if (/.*found (\d+) rules*/) { $nrules = $1; }
    if (/.*?(\d+) schemas to inspect*/) { $nschemas = $1; }
    if (/nschemas = (\d+), min length = (\d+), max length = (\d+), avg length = (\d+)/) {
        $nschemas = $1; $minlen = $2; $maxlen = $3; $avglen = $4;
    }
    if (/min time = ([\d\.]+), max time = ([\d\.]+), avg time = ([\d\.]+)/) {
        $mintime = $1; $maxtime = $2; $avgtime = $3;
    }
    if (/found (\d+) non-trivial SCCs/) { $nsccs = $1; }
}

print "40:post-usersec=${b_user}|41:post-syssec=${b_sys}\
|42:post-elapsedsec=${b_elapsed}|43:post-maxreskb=${b_maxres}\
|45:post-bound=${bound}|46:post-unlocking=${unlocking}\
|47:post-locking=${locking}|48:post-nlocs=${nlocs}\
|49:post-nrules=${nrules}\
|52:post-nschemas=${nschemas}\
|53:post-minlen=${minlen}|54:post-maxlen=${maxlen}\
|55:post-avglen=${avglen}|56:post-nsccs=${nsccs}\
|60:post-mintime=${mintime}|61:post-maxtime=${maxtime}\
|62:post-avgtime=${avgtime}\n"
'`

    echo "10:Result=$res|$stat"
}

