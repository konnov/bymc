#!/bin/sh

PROG=$1
PROP=$2

SPIN=spin601
cmd=""

CAMLRUNPARAM="b" ./run.native -a $PROG

while [ "$cmd" != "q" ]; do
    $SPIN -a -N $PROP abs-counter.prm \
        && gcc -o ./pan pan.c && ./pan -a -m1000000 \
        && $SPIN -t -N $PROP abs-counter.prm | grep 'GS{' | tee out  \
        && CAMLRUNPARAM="b" ./run.native -t out $PROG

    echo -n "     0  "; head -n 1 out # start with 0
    tail -n '+2' out | cat -n

    echo "Enter to continue, q<Enter> to exit"
    read cmd
done
