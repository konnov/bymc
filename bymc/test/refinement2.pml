/**
 A complex test of two proctypes communicating via nsnt.
 */

#define FALSE   0
#define TRUE    1

symbolic int T; /* the threshold */

int nsnt;

assume(T > 1);

atomic exA = some(A:pc == 2);
atomic allA = all(A:pc == 2);
atomic prec_initA = all(A@end);
atomic in_transitA = some(A:nrcvd < nsnt);
atomic in_transitB = some(B:nrcvd < nsnt);
atomic exB = some(B:pc == 2);
atomic allB = all(B:pc == 2);
atomic prec_initB = all(B@end);
atomic in_transitB = some(B:nrcvd < nsnt);

active[T] proctype A() {
    byte pc = 0, next_pc = 0;
    int nrcvd = 0, next_nrcvd = 0;

    /* INIT */
    if
        :: pc = 0;
    fi;

    /* THE ALGORITHM */
end: /* at some point there will be nothing to do */
    do
        :: atomic {
            if
                :: next_nrcvd = nrcvd + 1;
                :: next_nrcvd = nrcvd;
            fi;
            if
                :: next_nrcvd > nsnt ->
                   next_nrcvd = nrcvd;
                :: else;
            fi;
            if
                :: pc == 0 -> next_pc = 1;
                :: pc == 1 && next_nrcvd >= 2 * T -> next_pc = 2;
                :: else -> next_pc = pc;
            fi;
            if
                :: (pc == 0) && (next_pc == 1) -> nsnt++;
                :: (pc == 1) && (next_pc == 2) -> nsnt++;
                :: else;
            fi;
            pc = next_pc;
            nrcvd = next_nrcvd;
            next_pc = 0;
            next_nrcvd = 0;
        }
    od;
}

active[T] proctype B() {
    byte pc = 0, next_pc = 0;
    int nrcvd = 0, next_nrcvd = 0;

    /* INIT */
    if
        :: pc = 0;
    fi;

    /* THE ALGORITHM */
end: /* at some point there will be nothing to do */
    do
        :: atomic {
            if
                :: next_nrcvd = nrcvd + 1;
                :: next_nrcvd = nrcvd;
            fi;
            if
                :: next_nrcvd > nsnt ->
                   next_nrcvd = nrcvd;
                :: else;
            fi;
            if
                :: pc == 0 && next_nrcvd >= T -> next_pc = 1;
                :: pc == 1 && next_nrcvd >= 3 * T -> next_pc = 2;
                :: else -> next_pc = pc;
            fi;
            if
                :: (pc == 0) && (next_pc == 1) -> nsnt++;
                :: (pc == 1) && (next_pc == 2) -> nsnt++;
                :: else;
            fi;
            pc = next_pc;
            nrcvd = next_nrcvd;
            next_pc = 0;
            next_nrcvd = 0;
        }
    od;
}

ltl fairness { []<>(!in_transitA /*&& !in_transitB*/) }
ltl unforg { [](in_transitA -> !allA) }
ltl progall { [](prec_initA -> <>allA) }
ltl progex { [](prec_initA -> <>exA) }

/*
#BEGIN-TEST progall
$bymc_dir/verifypa-spin ${testsource} progall
#EXPECT grep "no-refinement" ${testlog}
#END-TEST

#DISABLED-TEST unforg
$bymc_dir/verifypa-spin ${testsource} unforg
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST
*/

