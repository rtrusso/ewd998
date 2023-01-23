---- MODULE HourClock ----

EXTENDS Integers
VARIABLE Hour, AmPm

Init ==
    /\ Hour \in 1..12
    /\ AmPm \in {"AM", "PM"}

Next ==
    /\ IF Hour = 12
       THEN Hour' = Hour -12 + 1
       ELSE Hour' = Hour + 1
    /\ IF Hour = 12
       THEN IF AmPm = "AM"
            THEN AmPm' = "PM"
            ELSE AmPm' = "AM"
       ELSE UNCHANGED AmPm

HourIsValid == Hour \in 1..12


====