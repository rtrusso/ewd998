---- MODULE HourClock2 ----

EXTENDS Integers
VARIABLE Hour
vars == <<Hour>>

Init ==
    /\ Hour \in 1..12

Next ==
    /\ IF Hour = 12
       THEN Hour' = 1
       ELSE Hour' = Hour + 1

HourIsValid == Hour \in 1..12

\* This is a comment

(*
This is also a comment
*)

MyProperty ==
    /\ [][/\ Hour = 11 => Hour' = 12]_vars

AllHoursAreReachable == \A hour \in 1..12 : []<>(Hour = hour)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
 
====
