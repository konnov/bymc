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

    /* INIT */
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
    ltl relay { ([](ex_acc -> <>(all_acc))) }
    ltl corr { (prec_corr -> <>(ex_acc)) }
    ltl unforg { (prec_unforg -> [](!ex_acc)) }
#endif

/*
#BEGIN-TEST correct-unforg
$bymc_dir/verifypa-spin ${testsource} unforg -O smt.log=1
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST

#BEGIN-TEST correct-relay
$bymc_dir/verifypa-spin ${testsource} relay -O smt.log=1
#EXPECT grep -e "verified in [1-9]\([0-9]\)* refinement" ${testlog}
#END-TEST

#BEGIN-TEST correct-corr
$bymc_dir/verifypa-spin ${testsource} corr -O smt.log=1
#EXPECT grep "verified in [1-9]\([0-9]\)* refinement" ${testlog}
#END-TEST

#BEGIN-TEST f_LE_t_P_1-unforg
$bymc_dir/verifypa-spin ${testsource} unforg -D BUG=1 -O smt.log=1
#EXPECT grep "no-refinement" ${testlog}
#END-TEST

#BEGIN-TEST n_GE_3t-relay
$bymc_dir/verifypa-spin ${testsource} relay -D NGE3T=1 -O smt.log=1
#EXPECT grep "no-refinement" ${testlog}
#END-TEST

#BEGIN-TEST concrete-correct-unforg
$bymc_dir/verifyco-spin 'N=4,T=1,F=1' ${testsource} unforg
#EXPECT grep "errors:.*0" ${testlog}
#END-TEST

#BEGIN-TEST concrete-correct-unforg-too-many-faults
$bymc_dir/verifyco-spin 'N=4,T=1,F=2' ${testsource} unforg
#EXPECT grep "errors:.*1" ${testlog}
#END-TEST

#BEGIN-TEST concrete-correct-relay
$bymc_dir/verifyco-spin 'N=4,T=1,F=1' ${testsource} relay
#EXPECT grep "errors:.*0" ${testlog}
#END-TEST

#BEGIN-TEST concrete-correct-relay-too-many-faults
$bymc_dir/verifyco-spin 'N=4,T=1,F=2' ${testsource} relay
#EXPECT grep "errors:.*1" ${testlog}
#END-TEST

#BEGIN-TEST concrete-correct-corr
$bymc_dir/verifyco-spin 'N=4,T=1,F=1' ${testsource} corr
#EXPECT grep "errors:.*0" ${testlog}
#END-TEST

#BEGIN-TEST concrete-correct-corr-too-many-faults
$bymc_dir/verifyco-spin 'N=4,T=1,F=2' ${testsource} corr
#EXPECT grep "errors:.*1" ${testlog}
#END-TEST

#BEGIN-TEST correct-bdd-unforg
$bymc_dir/verifypa-nusmv-bdd ${testsource} unforg -O smt.log=1
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST

#BEGIN-TEST correct-bdd-relay
$bymc_dir/verifypa-nusmv-bdd ${testsource} relay -O smt.log=1
#EXPECT grep -e "verified in [1-9]\([0-9]\)* refinement" ${testlog}
#END-TEST

#BEGIN-TEST correct-bdd-corr
$bymc_dir/verifypa-nusmv-bdd ${testsource} corr -O smt.log=1
#EXPECT grep "verified in [1-9]\([0-9]\)* refinement" ${testlog}
#END-TEST

#BEGIN-TEST f_LE_t_P_1-bdd-unforg
$bymc_dir/verifypa-nusmv-bdd ${testsource} unforg -D BUG=1 -O smt.log=1
#EXPECT grep "no-refinement" ${testlog}
#END-TEST

#BEGIN-TEST n_GE_3t-bdd-relay
$bymc_dir/verifypa-nusmv-bdd ${testsource} relay -D NGE3T=1 -O smt.log=1
#EXPECT grep "no-refinement" ${testlog}
#END-TEST

#BEGIN-TEST correct-bmc-unforg
$bymc_dir/verifypa-nusmv-bmc --length 50 ${testsource} unforg -O smt.log=1
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST

#BEGIN-TEST correct-bmc-relay
$bymc_dir/verifypa-nusmv-bmc --length 50 ${testsource} relay -O smt.log=1
#EXPECT grep -e "verified in [1-9]\([0-9]\)* refinement" ${testlog}
#END-TEST

#BEGIN-TEST correct-bmc-corr
$bymc_dir/verifypa-nusmv-bmc --length 50 ${testsource} corr -O smt.log=1
#EXPECT grep "verified in [1-9]\([0-9]\)* refinement" ${testlog}
#END-TEST

#BEGIN-TEST f_LE_t_P_1-bmc-unforg
$bymc_dir/verifypa-nusmv-bmc --length 50 ${testsource} unforg -D BUG=1 -O smt.log=1
#EXPECT grep "no-refinement" ${testlog}
#END-TEST

#BEGIN-TEST n_GE_3t-bmc-relay
$bymc_dir/verifypa-nusmv-bmc --length 50 ${testsource} relay -D NGE3T=1 -O smt.log=1
#EXPECT grep "no-refinement" ${testlog}
#END-TEST




#BEGIN-TEST z3-correct-unforg
$bymc_dir/verifypa-spin ${testsource} unforg --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-correct-relay
$bymc_dir/verifypa-spin ${testsource} relay --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep -e "verified in [1-9]\([0-9]\)* refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-correct-corr
$bymc_dir/verifypa-spin ${testsource} corr --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep "verified in [1-9]\([0-9]\)* refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-f_LE_t_P_1-unforg
$bymc_dir/verifypa-spin ${testsource} unforg -D BUG=1 --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep "no-refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-n_GE_3t-relay
$bymc_dir/verifypa-spin ${testsource} relay -D NGE3T=1 --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep "no-refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-concrete-correct-unforg
$bymc_dir/verifyco-spin 'N=4,T=1,F=1' ${testsource} unforg --smt 'lib2|z3|-smt2|-in'
#EXPECT grep "errors:.*0" ${testlog}
#END-TEST

#BEGIN-TEST z3-concrete-correct-unforg-too-many-faults
$bymc_dir/verifyco-spin 'N=4,T=1,F=2' ${testsource} unforg --smt 'lib2|z3|-smt2|-in'
#EXPECT grep "errors:.*1" ${testlog}
#END-TEST

#BEGIN-TEST z3-concrete-correct-relay
$bymc_dir/verifyco-spin 'N=4,T=1,F=1' ${testsource} relay --smt 'lib2|z3|-smt2|-in'
#EXPECT grep "errors:.*0" ${testlog}
#END-TEST

#BEGIN-TEST z3-concrete-correct-relay-too-many-faults
$bymc_dir/verifyco-spin 'N=4,T=1,F=2' ${testsource} relay --smt 'lib2|z3|-smt2|-in'
#EXPECT grep "errors:.*1" ${testlog}
#END-TEST

#BEGIN-TEST z3-concrete-correct-corr
$bymc_dir/verifyco-spin 'N=4,T=1,F=1' ${testsource} corr --smt 'lib2|z3|-smt2|-in'
#EXPECT grep "errors:.*0" ${testlog}
#END-TEST

#BEGIN-TEST z3-concrete-correct-corr-too-many-faults
$bymc_dir/verifyco-spin 'N=4,T=1,F=2' ${testsource} corr --smt 'lib2|z3|-smt2|-in'
#EXPECT grep "errors:.*1" ${testlog}
#END-TEST

#BEGIN-TEST z3-correct-bdd-unforg
$bymc_dir/verifypa-nusmv-bdd ${testsource} unforg --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-correct-bdd-relay
$bymc_dir/verifypa-nusmv-bdd ${testsource} relay --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep -e "verified in [1-9]\([0-9]\)* refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-correct-bdd-corr
$bymc_dir/verifypa-nusmv-bdd ${testsource} corr --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep "verified in [1-9]\([0-9]\)* refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-f_LE_t_P_1-bdd-unforg
$bymc_dir/verifypa-nusmv-bdd ${testsource} unforg -D BUG=1 --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep "no-refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-n_GE_3t-bdd-relay
$bymc_dir/verifypa-nusmv-bdd ${testsource} relay -D NGE3T=1 --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep "no-refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-correct-bmc-unforg
$bymc_dir/verifypa-nusmv-bmc --length 50 ${testsource} unforg --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-correct-bmc-relay
$bymc_dir/verifypa-nusmv-bmc --length 50 ${testsource} relay --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep -e "verified in [1-9]\([0-9]\)* refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-correct-bmc-corr
$bymc_dir/verifypa-nusmv-bmc --length 50 ${testsource} corr --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep "verified in [1-9]\([0-9]\)* refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-f_LE_t_P_1-bmc-unforg
$bymc_dir/verifypa-nusmv-bmc --length 50 ${testsource} unforg -D BUG=1 --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep "no-refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-n_GE_3t-bmc-relay
$bymc_dir/verifypa-nusmv-bmc --length 50 ${testsource} relay -D NGE3T=1 --smt 'lib2|z3|-smt2|-in' -O smt.log=1
#EXPECT grep "no-refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-correct-post-cav15-opt-unforg
$bymc_dir/verifypa-post ${testsource} unforg --smt 'lib2|z3|-smt2|-in' -O smt.log=1 -O schema.tech=cav15-opt
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-f_LE_t_P_1-post-cav15-opt-unforg
$bymc_dir/verifypa-post ${testsource} unforg -D BUG=1 --smt 'lib2|z3|-smt2|-in' -O smt.log=1 -O schema.tech=cav15-opt
#EXPECT test ${texitcode} 1
#EXPECT grep "counterexample for unforg found" ${testlog}
#END-TEST

#BEGIN-TEST z3-correct-post-cav15-unforg
$bymc_dir/verifypa-post ${testsource} unforg --smt 'lib2|z3|-smt2|-in' -O smt.log=1 -O schema.tech=cav15
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-f_LE_t_P_1-post-cav15-unforg
$bymc_dir/verifypa-post ${testsource} unforg -D BUG=1 --smt 'lib2|z3|-smt2|-in' -O smt.log=1 -O schema.tech=cav15
#EXPECT test ${texitcode} 1
#EXPECT grep "counterexample for unforg found" ${testlog}
#END-TEST

#BEGIN-TEST z3-correct-post-ltl-unforg
$bymc_dir/verifypa-post ${testsource} unforg --smt 'lib2|z3|-smt2|-in' -O smt.log=1 -O schema.tech=ltl
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-f_LE_t_P_1-post-ltl-unforg
$bymc_dir/verifypa-post ${testsource} unforg -D BUG=1 --smt 'lib2|z3|-smt2|-in' -O smt.log=1 -O schema.tech=ltl
#EXPECT test ${texitcode} 1
#EXPECT grep "counterexample for unforg found" ${testlog}
#END-TEST
*/

