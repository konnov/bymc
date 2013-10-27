#!/bin/bash
#
# Functional tests

bymc_dir=`dirname $0`
export bymc_dir=`cd $bymc_dir/.. && pwd`
export run_dir="$bymc_dir/_test-run"
logfile="$run_dir/test.log"

if [ "${run_dir}" != "" -a -d "$run_dir" ]; then
    rm -rf "$run_dir"
fi

mkdir "$run_dir" && cd "$run_dir"

for f in $bymc_dir/test/*.pml; do
    ${bymc_dir}/test/extract-tests.py "$f"
done

nok=0
nfail=0

for t in *.test; do
    tlog=`echo $t | sed 's/.test/.log/'`
    terr=`echo $t | sed 's/.test/.err/'`
    teva=`echo $t | sed 's/.test/.eval/'`
    echo "TEST $t"
    echo "TEST $t" >>$logfile
    echo "$t >$tlog" >>$logfile
    export testlog="$tlog"
    export AUTO=1
    sh >"${tlog}" 2>${terr} $t
    if [ "$?" != "0" ]; then
        echo "FAILED"
        echo "FAILED to exec. Check $tlog" >>$logfile
        nfail=$((nfail+1))
    else
        sh $teva $tlog >>$logfile
        if [ "$?" != "0" ]; then
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

echo "FAILED: $nfail OK: $nok"
echo "Check $logfile for details"

