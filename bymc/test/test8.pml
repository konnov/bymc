/**
 * A test inspired by a bug caused by conditional consensus
 */

#define V0      0 /* the initial state */
#define P0      1 /* in phase 1 */
#define P1      2 /* in phase 2 */

#define FALSE   0
#define TRUE    1

symbolic int N; /* the number of processes: correct + faulty */
symbolic int T; /* the threshold */
symbolic int F; /* the actual number of faulty processes */

int nsnt00, nsnt10;
int nsnt01;

assume(N > 2);
assume(F >= 0);
assume(T >= 1);
assume(N > 2 * T);
assume(F <= T);

/* two orders between the thresholds are possible: */
assume (F >= 1);
/* and:
assume (F == 0);
 */

atomic prec_no0 = all(Proc:pc != V0);


atomic all_not_in_p0 = all(Proc:pc != P0);
atomic all_not_in_p1 = all(Proc:pc != P1);

active[N] proctype Proc() {
    byte pc = 0, next_pc = 0;
    int nrcvd00 = 0, next_nrcvd00 = 0;
    int nrcvd01 = 0, next_nrcvd01 = 0;
    int nrcvd10 = 0, next_nrcvd10 = 0;

    /* INIT */
    pc = V0;
    
end:
    do
        :: atomic {
                if
                :: (pc == V0 || pc == P0) ->
                    havoc(next_nrcvd00);
                    assume (nrcvd00 <= next_nrcvd00 && next_nrcvd00 <= nsnt00);
                    havoc(next_nrcvd01);
                    assume (nrcvd01 <= next_nrcvd01 && next_nrcvd01 <= nsnt01);
                :: else -> next_nrcvd00 = nrcvd00; next_nrcvd01 = nrcvd01;
                fi;
                if
   	            :: pc == P1 ->
                    havoc(next_nrcvd10);
                    assume (nrcvd10 <= next_nrcvd10 && next_nrcvd10 <= nsnt10);
                :: else -> next_nrcvd10 = nrcvd10;
                fi;

            	/* a step by FSM */
            	/* find the next value of the program counter */
            	if
                    :: pc == V0 ->
                        next_pc = P0;
               	    :: (pc == P0) && (next_nrcvd00 >= N - T ) ->
                        nsnt10++; next_nrcvd00 = 0; next_nrcvd01 = 0;
                    	next_pc = P1;
               	    :: (pc == P0) && (next_nrcvd01 >= N - T ) ->
                        nsnt10++; next_nrcvd00 = 0; next_nrcvd01 = 0;
                    	next_pc = P1;
                    :: else ->
                    	next_pc = pc;
            	fi;
            	/* send the echo message */
            	if
                	:: (pc == V0) && (next_pc == P0)  ->
                        nsnt00++;
                        nsnt01++;
                	:: else;
            	fi;


            pc = next_pc;
            nrcvd00 = next_nrcvd00;
            nrcvd01 = next_nrcvd01;
            nrcvd10 = next_nrcvd10;
            next_pc = 0;
            next_nrcvd00 = 0;
            next_nrcvd01 = 0;
            next_nrcvd10 = 0;
        }
    od;
}


ltl unreach_p0 { ([] all_not_in_p0) }
ltl unreach_p1 { ([] all_not_in_p1) }

