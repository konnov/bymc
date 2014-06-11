/**
 * A parameterized model of the broadcast distributed algorithm 
 * in the symbolic extension of Promela.
 *
 * This file was modified for the purposes of functional testing,
 * e.g., it can have bugs introduced deliberately for the testing purposes.
 * Do not use it elsewhere. The original code is distributed from the tool's
 * website.
 *
 * Igor Konnov, Josef Widder, 2012-2014.
 *
 * This file is a subject to the license that is bundled
 * together with this package and can be found in the file LICENSE.
 */

#pragma option "bymc.version = 0.6.0"

#define V0      0 /* the initial state */
#define V1      1 /* the init message received */
#define SE      2 /* the echo message sent */
#define AC      3 /* the accepting state */
#define PC_SZ   4

#define FALSE   0
#define TRUE    1

symbolic int N; /* the number of processes: correct + faulty */
symbolic int T; /* the threshold */
symbolic int F; /* the actual number of faulty processes */

int nsnt = 0;

#ifdef NGE3T
assume(N >= 3 * T); /* this condition leads to starvation */
#else
assume(N > 3 * T);
#endif

assume(N > 3);
assume(F >= 0);
assume(T >= 1);

#ifdef BUG
assume(F <= T + 1); /* this condition violates unforgeability */
#else
assume(F <= T);
#endif

atomic prec_unforg = all(Proc:pc == V0);
atomic prec_corr = all(Proc:pc == V1);
atomic prec_init = all(Proc@end);
atomic ex_acc = some(Proc:pc == AC);
atomic all_acc = all(Proc:pc == AC);
atomic in_transit = some(Proc:nrcvd < nsnt);
atomic tx_inv = ((card(Proc:pc == SE) + card(Proc:pc == AC)) == nsnt);

active[N - F] proctype Proc() {
    byte pc = 0; int nrcvd = 0;
    byte next_pc = 0; int next_nrcvd = 0;

    /* INV0 */
    if
        ::pc = V0;
        ::pc = V1;
    fi;

    /* THE ALGORITHM */
end: /* at some point there will be nothing to do */
    do
        :: atomic {
#ifndef SPIN
            havoc(next_nrcvd);
            assume(nrcvd <= next_nrcvd && next_nrcvd <= nsnt + F);
#else
            if
                :: next_nrcvd = nrcvd + 1;  /* receive */
                :: next_nrcvd = nrcvd;      /* no receive in this step */
            fi;
            if
	            :: !(next_nrcvd <= nsnt + F)  ->
                    next_nrcvd = nrcvd; /* forget the new value */
                :: else;
            fi;
#endif
            /* a step by FSM */
            if /* find the next value of the program counter */
                :: next_nrcvd >= N - T ->
                    next_pc = AC;
                :: next_nrcvd < N - T && (pc == V1 || next_nrcvd >= T + 1) ->
                    next_pc = SE;
                :: else ->
                    next_pc = pc;
            fi;
            if /* send the echo message */
                :: (pc == V0 || pc == V1) && (next_pc == SE || next_pc == AC) ->
                    nsnt++;
                :: else;
            fi;

            pc = next_pc;
            nrcvd = next_nrcvd;
#ifdef SPIN
            printf("STEP: pc=%d; nrcvd=%d; nsnt=%d\n", pc, nrcvd, nsnt);
#endif
            next_pc = 0;        /* decrease state space */
            next_nrcvd = 0;

        }
    od;
}

ltl fairness { []<>(!in_transit) }
#ifdef SPIN
    ltl relay { [](ex_acc -> <>all_acc) }
    ltl corr { []((prec_init && prec_corr) -> <>(ex_acc)) }
    ltl unforg { []((prec_init && prec_unforg) -> []!ex_acc) }
#else
    ltl relay { (ex_acc -> <>(all_acc)) }
    ltl corr { (prec_corr -> <>(ex_acc)) }
    ltl unforg { (prec_unforg -> [](!ex_acc)) }
#endif

/*
#BEGIN-TEST correct-unforg
$bymc_dir/verifypa-spin ${testsource} unforg
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST

#BEGIN-TEST correct-relay
$bymc_dir/verifypa-spin ${testsource} relay
#EXPECT grep -e "verified in [1-9]\([0-9]\)* refinement" ${testlog}
#END-TEST

#BEGIN-TEST correct-corr
$bymc_dir/verifypa-spin ${testsource} corr
#EXPECT grep "verified in [1-9]\([0-9]\)* refinement" ${testlog}
#END-TEST

#BEGIN-TEST f_LE_t_P_1-unforg
$bymc_dir/verifypa-spin ${testsource} unforg -D BUG=1
#EXPECT grep "no-refinement" ${testlog}
#END-TEST

#BEGIN-TEST n_GE_3t-relay
$bymc_dir/verifypa-spin ${testsource} relay -D NGE3T=1
#EXPECT grep "no-refinement" ${testlog}
#END-TEST
*/
