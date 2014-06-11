#!/bin/bash
#
# The script to extract and run functional tests.
#
# This script is as minimal as possible. No overgrown frameworks please.
#
# Igor Konnov, 2013-2014.

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
ndisabled=0

for t in ${args:-*.test}; do
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
    sh >"${tlog}" 2>${terr} $t
    if [ ! -x "$t" -o "$?" != "0" ]; then
        echo "FAILED"
        echo "FAILED to exec. Check $tlog" >>$logfile
        nfail=$((nfail+1))
    else
        sh $teva $tlog >>$logfile
        ret="$?"
        if [ "$ret" == "101" ]; then
            echo "DISABLED"
            ndisabled=$((ndisabled+1))
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

echo "FAILED: $nfail DISABLED: $ndisabled OK: $nok"
echo "Check $logfile for details"

