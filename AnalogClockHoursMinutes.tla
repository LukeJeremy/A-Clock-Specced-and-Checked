---------------------- MODULE AnalogClockHoursMinutes ----------------------

EXTENDS Integers, Naturals

VARIABLES h, m

vars == <<h, m>>

Init == /\ h \in 0..23
        /\ m \in 0..59

Tick == IF h = 23 /\ m = 59
        THEN /\ h' = 0
             /\ m' = 0
        ELSE IF m = 59
             THEN /\ h' = h + 1
                  /\ m' = 0
             ELSE /\ m' = m + 1
                  /\ UNCHANGED<<h>> 

(* INVARIANTS *)
TypeOK == /\ h \in 0..23
          /\ m \in 0..59
          
(* TEMPORAL PROPERTIES *)

Incremental(x, y) == x' # x /\ x' # 0 => x' = x + y

ClockIncrementsByAtMostOne == 
[][Incremental(h, 1) /\ Incremental(m, 1)]_vars

ClockResetsAtMidnight == []<><</\ h = 23
                               /\ h' = 0
                               /\ m = 59
                               /\ m' = 0>>_vars
(* SPEC *)
(* Weak Fairness prevents infinite stuttering from *)
(* violating the temporal formula ClockResetsAtMidnight *)
Spec == Init /\ [][Tick]_vars /\ WF_vars(Tick)

THEOREM Spec => []TypeOK
THEOREM Spec => ClockIncrementsByAtMostOne

=============================================================================
\* Modification History
\* Last modified Sat Jul 13 19:49:22 AEST 2019 by luke
\* Created Thu Jul 11 19:08:26 AEST 2019 by luke
