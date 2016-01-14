/**
 * One-step consensus that one can find, e.g., in:
 *
 * D. Dobre, N. Suri. One-step Consensus with Zero-Degradation.
 * (Algorithm 2, lines 1--4).
 *
 * Here we consider only the algorithm itself, without looking
 * at the underlying consensus.
 *
 * Igor Konnov, Josef Widder, 2014
 *
 * This file is a subject to the license that is bundled
 * together with this package and can be found in the file LICENSE.
 */

#define V0      0 /* the initial state with value 0 */
#define V1      1 /* the initial state with value 1 */
#define S0      2 /* sent vote 0 */
#define S1      3 /* sent vote 1 */
#define D0      4 /* decided on 0 */
#define D1      5 /* decided on 1 */
#define U0      6 /* called underlying consensus with value 0 */
#define U1      7 /* called underlying consensus with value 1 */
#define CR      8 /* crashed */

symbolic int N;     /* the number of processes: correct + faulty */
symbolic int T;     /* the threshold */
symbolic int F;     /* crashes */

int nsnt0, nsnt1;
int nsnt0F, nsnt1F; /* the messages sent by faulty processes */
int nfaulty;        /* the number of faulty processes */

assume(N > 3);
assume(F >= 0);
assume(T >= 1);

#ifndef BUG2
assume(N > 3 * T);
#else
assume(N >= 3 * T);
#endif

#ifdef CASE3
    /* case 3 */
    assume(F > 1);
#else
    #ifdef CASE2
        /* case 2 */
        assume(F == 1);
    #else
        /* case 1 */
        assume(F == 0);
    #endif
#endif

#ifndef FeqTp1
assume(F <= T);
#else
assume(F <= T + 1);
#endif

/* the initial states that guarantee one-step consensus */
atomic all_at_V0 = all(Proc:pc == V0);
atomic all_at_V1 = all(Proc:pc == V1);

/* The authors claim that n - t will also work. Let's check */
atomic almost_all_at_V0 =
    (card(Proc:pc == V0 && Proc:nrcvd0 == 0 && Proc:nrcvd1 == 0) == N - T);
atomic almost_all_at_V1 =
    (card(Proc:pc == V1 && Proc:nrcvd0 == 0 && Proc:nrcvd1 == 0) == N - T);

atomic all_at_D0_or_CR = all(Proc:pc == D0 || Proc:pc == CR);
atomic all_at_D1_or_CR = all(Proc:pc == D1 || Proc:pc == CR);

atomic all_not_at_D0 = all(Proc:pc != D0);
atomic all_not_at_D1 = all(Proc:pc != D1);
atomic all_not_at_U0 = all(Proc:pc != U0);
atomic all_not_at_U1 = all(Proc:pc != U1);

atomic in_transit0 = some(Proc:nrcvd0 < nsnt0);
atomic in_transit1 = some(Proc:nrcvd1 < nsnt1);

active[N - F] proctype Proc() {
    byte pc = 0, next_pc = 0;
    int nrcvd0 = 0, next_nrcvd0 = 0;
    int nrcvd1 = 0, next_nrcvd1 = 0;

    /* INIT */
    if
        :: pc = V0;
        :: pc = V1;
    fi;
    
end:
    do
        :: atomic {
#ifndef SPIN /* NUSMV or a symbolic encoding */
            if
                :: pc == V0 || pc == V1 || pc == S0 || pc == S1 ->
                /* receive votes */
                havoc(next_nrcvd0);
            	assume(nrcvd0 <= next_nrcvd0 && next_nrcvd0 <= nsnt0 + nsnt0F);
                havoc(next_nrcvd1);
            	assume(nrcvd1 <= next_nrcvd1 && next_nrcvd1 <= nsnt1 + nsnt1F);

                :: pc == D0 || pc == D1 || pc == U0 || pc == U1 || pc == CR ->
                /* no need to count messages any more */
                next_nrcvd0 = 0;
                next_nrcvd1 = 0;
            fi;
#else /* SPIN */
                if  :: (nrcvd0 < nsnt0) ->
                        next_nrcvd0 = nrcvd0;
                    :: next_nrcvd0 = nrcvd0;
                fi;
                if  :: (nrcvd1 < nsnt1) ->
                        next_nrcvd1 = nrcvd1 + 1;
                    :: next_nrcvd1 = nrcvd1;
                fi;
#endif

            	/* a step by FSM */
            	if
                    /* send the input */
                    :: pc == V0 ->
                        next_pc = S0;

                    :: pc == V1 ->
                        next_pc = S1;

                    :: (pc == S0 || pc == S1)
                            && next_nrcvd0 + next_nrcvd1 >= N - T ->
                        if
                            /* decide immediately */

                            :: next_nrcvd0 >= N - T -> next_pc = D0;

                            :: next_nrcvd1 >= N - T -> next_pc = D1;

                            :: next_nrcvd0 < N - T && next_nrcvd1 < N - T ->
                                if
                                    /* the input value falls through to
                                        the underlying consensus */
                                    :: pc == S0 ->
                                        next_pc = U0;

                                    :: pc == S1 ->
                                        next_pc = U1;
                                fi;
                        fi;

                    :: nfaulty < F ->
                        /* crash */
                        nfaulty++;
                        next_pc = CR;

                    :: (pc != V0 && pc != V1 && pc != S0 && pc != S1)
                            || nrcvd0 + nrcvd1 < N - T ->
                        /* keep */
                    	next_pc = pc;
            	fi;
            	/* send votes */
            	if
                	:: pc == V0 && next_pc == S0 -> nsnt0++;

                	:: pc == V1 && next_pc == S1 -> nsnt1++;

                	:: pc == V0 && next_pc == CR -> nsnt0F++;

                	:: pc == V1 && next_pc == CR -> nsnt1F++;

#ifdef BUG1
                    /* introduce a bug in the code */
                	:: pc == V0 && next_pc == CR -> nsnt1F++;
#endif

                	:: else;
            	fi;

            pc = next_pc;
            nrcvd0 = next_nrcvd0;
            nrcvd1 = next_nrcvd1;
            next_pc = 0;
            next_nrcvd0 = 0;
            next_nrcvd1 = 0;
        }
    od;
}

ltl fairness { []<>(!in_transit0) && []<>(!in_transit1) }

#ifdef SPIN
#else
    ltl one_step0 { all_at_V0 ->
        [](all_not_at_D1 && all_not_at_U0 && all_not_at_U1) }
    ltl one_step1 { all_at_V1 ->
        [](all_not_at_D0 && all_not_at_U0 && all_not_at_U1) }
#endif

/*
#BEGIN-TEST z3-correct-post-ltl-onestep0
$bymc_dir/verifypa-post ${testsource} one_step0 --smt 'lib2|z3|-smt2|-in' -O smt.log=1 -D CASE2=1 -O schema.tech=ltl
#EXPECT test ${texitcode} 0
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-FeqTp1-post-ltl-onestep0
$bymc_dir/verifypa-post ${testsource} one_step0 --smt 'lib2|z3|-smt2|-in' -O smt.log=1 -D CASE2=1 -D BUG1=1 -O schema.tech=ltl
#EXPECT test ${texitcode} 1
#EXPECT grep "counterexample for one_step0 found" ${testlog}
#END-TEST

#BEGIN-TEST z3-correct-post-cav15-onestep0
$bymc_dir/verifypa-post ${testsource} one_step0 --smt 'lib2|z3|-smt2|-in' -O smt.log=1 -D CASE2=1 -O schema.tech=cav15
#EXPECT test ${texitcode} 0
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-FeqTp1-post-cav15-onestep0
$bymc_dir/verifypa-post ${testsource} one_step0 --smt 'lib2|z3|-smt2|-in' -O smt.log=1 -D CASE2=1 -D BUG1=1 -O schema.tech=cav15
#EXPECT test ${texitcode} 1
#EXPECT grep "counterexample for one_step0 found" ${testlog}
#END-TEST

#BEGIN-TEST z3-correct-post-cav15-opt-onestep0
$bymc_dir/verifypa-post ${testsource} one_step0 --smt 'lib2|z3|-smt2|-in' -O smt.log=1 -D CASE2=1 -O schema.tech=cav15-opt
#EXPECT test ${texitcode} 0
#EXPECT grep "verified in 0 refinement" ${testlog}
#END-TEST

#BEGIN-TEST z3-FeqTp1-post-cav15-opt-onestep0
$bymc_dir/verifypa-post ${testsource} one_step0 --smt 'lib2|z3|-smt2|-in' -O smt.log=1 -D CASE2=1 -D BUG1=1 -O schema.tech=cav15-opt
#EXPECT test ${texitcode} 1
#EXPECT grep "counterexample for one_step0 found" ${testlog}
#END-TEST
*/

