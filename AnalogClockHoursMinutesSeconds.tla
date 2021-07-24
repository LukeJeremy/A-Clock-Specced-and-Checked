------------------- MODULE AnalogClockHoursMinutesSeconds -------------------
(*
It seems obvious to me that in any sensible definition of implementation,
a clock that displays hours, minutes, and seconds should implement the
specification of a clock that displays hours and minutes. I realized in 1983
that the simplest way to ensure that this is true is to require that all
specifications allow stuttering steps—steps in which the state of the system
does not change.

Steps of an hour/minute/second clock in which only the seconds change
implement stuttering steps of the hour/minute clock's specification.
In the decades since then, I have continued to explain this to people.
To my knowledge, no state-based specification formalism other than TLA
has adopted the idea. I suspect that even many TLA+ users think it's weird
to require that specifications allow stuttering steps.

Leslie Lamport
https://lamport.azurewebsites.net/tla/advanced.html
*)

EXTENDS Integers, Naturals

VARIABLES h, m, s

vars == <<h, m, s>>

Init == /\ h \in 0..23
        /\ m \in 0..59
        /\ s \in 0..59

(* AnalogClockHoursMinutes only allows increments by one *)
Tick == IF m = 3 /\ s = 59
        THEN /\ m' = 5
             /\ s' = 0
             /\ UNCHANGED<<h>>
        ELSE
        IF h = 23 /\ m = 59 /\ s = 59 
        THEN /\ h' = 0
             /\ m' = 0
             /\ s' = 0
        ELSE IF m = 59 /\ s = 59
             THEN /\ h' = h + 1
                  /\ m' = 0
                  /\ s' = 0
             ELSE IF s = 59
                  THEN /\ m' = m + 1
                       /\ s' = 0
                       /\ UNCHANGED<<h>>
                  ELSE /\ s' = s + 1
                       /\ UNCHANGED<<h, m>> 

(* INVARIANTS *)
TypeOK == /\ h \in 0..23
          /\ m \in 0..60
          /\ s \in 0..59
          
(* TEMPORAL PROPERTIES *)
ClockResetsAtMidnight == []<><</\ h = 23
                               /\ h' = 0
                               /\ m = 59
                               /\ m' = 0
                               /\ s = 59
                               /\ s' = 0>>_vars

(* SPEC *)
Spec == Init /\ [][Tick]_vars /\ WF_vars(Tick)

THEOREM Spec => []TypeOK

AnalogHoursMinutesClock == INSTANCE AnalogClockHoursMinutes WITH h <- h, m <- m
THEOREM Spec => AnalogHoursMinutesClock!Spec
=============================================================================
\* Modification History
\* Last modified Sat Jul 13 22:03:11 AEST 2019 by luke
\* Created Fri Jul 12 17:23:58 AEST 2019 by luke
