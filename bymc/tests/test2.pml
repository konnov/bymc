/**
 * A parameterized model of the broadcast distributed algorithm 
 * in the symbolic extension of Promela.
 *
 * Igor Konnov, Josef Widder, 2012
 */

#define IT      0 /* the initial state */
#define SE      1 /* the echo message sent */
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

atomic prec_unforg = all(Proc:pc == IT);
atomic prec_init = all(Proc@end);
atomic ex_acc = some(Proc:pc == SE);
atomic in_transit = some(Proc:nrcvd < nsnt);

active[N - F] proctype Proc() {
    byte pc = 0, next_pc = 0;
    int nrcvd = 0, next_nrcvd = 0;

    /* INIT */
    pc = IT;

    /* THE ALGORITHM */
end: /* at some point there will be nothing to do */
    do
        :: atomic {
            if
                :: nrcvd < 1 -> next_nrcvd = nrcvd + 1;
                :: else -> next_nrcvd = nrcvd;
            fi;
            if
                :: pc == 0 -> next_pc = 1;
                :: pc == 1 -> next_pc = 2;
                :: pc == 2 -> next_pc = 3;
                :: pc == 3 -> next_pc = pc;
            fi;
            nsnt = next_nrcvd;
            pc = next_pc;
            nrcvd = next_nrcvd;
            next_pc = 0;
            next_nrcvd = 0;
        }
    od;
}

ltl fairness { []<>(!in_transit) }
ltl unforg { []((prec_init && prec_unforg) -> []!ex_acc) }

