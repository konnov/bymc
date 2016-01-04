#!/bin/bash
#
# The script to extract and run functional tests.
#
# Run it with DRYRUN=1 ./func-test.sh, if you want to enumerate the tests without
# executing them.
#
# Check test/bcast-byz.pml for the syntax of the tests.
#
# This script is as minimal as possible. No overdeveloped frameworks please.
#
# Igor Konnov, 2013-2016.

bymc_dir=`dirname $0`
export bymc_dir=`cd $bymc_dir/.. && pwd`
export run_dir="$bymc_dir/_test-run"
logfile="$run_dir/test.log"

trap "exit 13" SIGHUP SIGINT SIGTERM

args="$@"

if [ "${run_dir}" != "" -a -d "$run_dir" ]; then
    rm -rf "$run_dir"
fi

mkdir "$run_dir" && cd "$run_dir"

for f in $bymc_dir/test/*.pml; do
    ${bymc_dir}/test/extract-tests.py "$f"
done

nok=0
nfail=0
nskip=0
ntodo=0
ntotal=0

start_time=`date '+%s'`

for t in ${args:-*.test}; do
    ntotal=$((ntotal+1))
    if echo "$t" | grep -v -q -e '.test$'; then
        t="$t.test" # in the case the test was specified manually
    fi

    tlog=`echo $t | sed 's/.test/.log/'`
    terr=`echo $t | sed 's/.test/.err/'`
    teva=`echo $t | sed 's/.test/.eval/'`
    echo "TEST $t"
    echo "TEST $t" >>$logfile
    echo "$t >$tlog" >>$logfile
    export testlog="$tlog"
    export AUTO=1
    if [ -f "$t" ]; then
        if [ -z "$DRYRUN" ]; then
            sh >"${tlog}" 2>${terr} $t
        else
            echo "Dry run: skipped ${t}" >> $logfile
            nskip=$((nskip+1))
        fi
    else
        false
    fi

    # a non-zero exit code can indicate the output, as in the sat solvers
    texitcode="$?"
    if [ "$texitcode" -ne 0 ]; then
        echo "A non-zero exit code ${texitcode}">>${terr}
    fi

    if [ -z "$DRYRUN" ]; then
        sh $teva $tlog >>$logfile
        ret="$?"
        if [ "$ret" == "101" ]; then
            echo "SKIPPED"
            nskip=$((nskip+1))
        elif [ "$ret" == "102" ]; then
            echo "TODO"
            ntodo=$((ntodo+1))
        elif [ "$ret" != "0" ]; then
            echo "FAILED"
            echo "FAILED. Check $tlog" >>$logfile
            nfail=$((nfail+1))
        else
            echo "OK"
            echo "OK" >>$logfile
            nok=$((nok+1))
        fi
    fi
done
end_time=`date '+%s'`
diff_time=$((end_time - start_time))

echo ""
echo "Check $logfile for details"
echo ""
echo "Ran: $ntotal tests in: $diff_time seconds"

# try to be compatible with the format by ounit
if [ "$nfail" -ne "0" ]; then
    echo "FAILED: Cases:$ntotal Tried:$((ntotal-nskip)) Errors:0 Failures:$nfail Skip:$nskip Todo:$ntodo Timeouts:0."
else
    echo "SUCCESS: Cases:$ntotal Tried:$((ntotal-nskip)) Errors:0 Failures:$nfail Skip:$nskip Todo:$ntodo Timeouts:0."
fi

