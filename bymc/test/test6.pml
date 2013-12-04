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

int nsntA;
int nsntB;

assume(N > 3);
assume(F >= 0);
assume(T >= 1);
assume(N > 3 * T);
assume(F <= T);

atomic prec_unforg = all(AProc:pc == 0);
atomic prec_init = all(AProc@end);
atomic ex_acc = some(AProc:pc == 0);
atomic in_transit = some(AProc:nrcvd < nsntA);

active[N - F] proctype AProc() {
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
                :: nrcvd < 1 -> next_nrcvd = nrcvd + 1;
                :: else -> next_nrcvd = nrcvd;
            fi;
            if
                :: next_pc = 1;
                :: next_pc = pc; /* pc never changes */
            fi;
            if
                :: nsntA == 0 -> nsntA++;
                :: else;
            fi;
            pc = next_pc;
            nrcvd = next_nrcvd;
            next_pc = 0;
            next_nrcvd = 0;
        }
    od;
}

active[N - F] proctype BProc() {
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
                :: nrcvd < 1 -> next_nrcvd = nrcvd + 1;
                :: else -> next_nrcvd = nrcvd;
            fi;
            if
                :: next_pc = 1;
                :: next_pc = pc; /* pc never changes */
            fi;
            if
                :: nsntB == 0 -> nsntB++;
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
ltl unforg { []((prec_init && prec_unforg) -> []!ex_acc) }

