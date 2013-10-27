/**
 A simple test, one pc, two intervals for received.
 */

#define IT      0 /* the initial state */
#define PC_SZ   4

#define FALSE   0
#define TRUE    1

symbolic int N; /* the number of processes: correct + faulty */
symbolic int T; /* the threshold */
symbolic int F; /* the actual number of faulty processes */

int nsnt;

assume(N > 3);
assume(F >= 0);
assume(T >= 1);
assume(N > 3 * T);
assume(F <= T);

atomic prec_unforg = all(Proc:pc == 0);
atomic prec_init = all(Proc@end);
atomic ex1 = some(Proc:pc == 1);
atomic all1 = all(Proc:pc == 1);
atomic in_transit = some(Proc:nrcvd < T);

active[N - F] proctype Proc() {
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
            /* this step is always infeasible in the counter
               abstraction, as it requires refinement on the level
               of the data abstraction. */
            if
                :: next_nrcvd = nrcvd + 1;
            fi;
            if
                :: next_nrcvd >= T + 1 -> next_pc = 1;
                :: else -> next_pc = 0;
            fi;
            if
                :: nrcvd < 1 -> nsnt++;
                :: else;
            fi;
            pc = next_pc;
            nrcvd = next_nrcvd;
            next_pc = 0;
            next_nrcvd = 0;
        }
    od;
}

ltl fairness { []<>(!in_transit) }
ltl unforg { [](in_transit -> !all1) }
ltl progall { [](prec_init -> <>all1) }
ltl progex { [](prec_init -> <>ex1) }

/*
#BEGIN-TEST
$bymc_dir/cegar ${testsource} unforg
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST
#BEGIN-TEST
$bymc_dir/cegar ${testsource} progall
#EXPECT grep "no-refinement" ${testlog}
#END-TEST
*/

