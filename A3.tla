--------------------- MODULE A3 ---------------------

EXTENDS Integers
CONSTANT NumberOfNodes 
\* CONSTANT TotalWork

VARIABLE NodeWorking
VARIABLE TerminationDetected
VARIABLE Network
\* VARIABLE WorkItemsDone

vars == <<NodeWorking, TerminationDetected, Network (*, WorkItemsDone*)>>

Nodes == 1..NumberOfNodes

TypeOk ==
    /\ Network \in [Nodes -> Nat]
    /\ NodeWorking \in [Nodes -> {TRUE, FALSE}]
    /\ TerminationDetected \in {TRUE, FALSE}
    (* /\ WorkItemsDone \in Nat
    /\ WorkItemsDone >= 0 *)
    \* /\ WorkItemsDone <= TotalWork

Terminated == 
    /\ \A node \in Nodes : NodeWorking[node] = FALSE
    /\ \A node \in Nodes : Network[node] = 0

Init ==
    /\ NodeWorking = [node \in Nodes |-> (node \div 2) * 2 = node ]
    /\ Network = [node \in Nodes |-> 0]
    /\ TerminationDetected = FALSE
    (* /\ WorkItemsDone = 0 *)

NodeFinishesWork(node) ==
    /\ NodeWorking[node] = TRUE
    /\ Network[node] = 0
    /\ NodeWorking' = [NodeWorking EXCEPT ![node] = FALSE]
    /\ UNCHANGED Network
    /\ UNCHANGED TerminationDetected
    (* /\ UNCHANGED WorkItemsDone *)

NodePassesToken(node) == 
    /\ TRUE
    /\ UNCHANGED Network
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED NodeWorking
    (* /\ UNCHANGED WorkItemsDone *)

DetectTermination == 
    /\ TerminationDetected = FALSE
    /\ Terminated
    /\ TerminationDetected' = TRUE
    /\ UNCHANGED Network
    /\ UNCHANGED NodeWorking
    (* /\ UNCHANGED WorkItemsDone *)

SendMessage(sourceNode) ==
    \E destinationNode \in Nodes :
      /\ NodeWorking[sourceNode] = TRUE
      /\ Network' = [Network EXCEPT ![destinationNode] = @ + 1]
      (* /\ WorkItemsDone' = WorkItemsDone + 1 *)
      \* /\ WorkItemsDone < TotalWork
      /\ UNCHANGED NodeWorking
      /\ UNCHANGED TerminationDetected

NodeReceives(sourceNode) ==
    /\ Network[sourceNode] > 0
    /\ Network' = [Network EXCEPT ![sourceNode] = @ - 1]
    /\ NodeWorking' = [NodeWorking EXCEPT ![sourceNode] = TRUE]
    /\ UNCHANGED TerminationDetected
    (* /\ UNCHANGED WorkItemsDone *)

NetworkIsFinite ==
    \A node \in Nodes : Network[node] <= 3

Next ==
    \E node \in Nodes :
        \/ NodeFinishesWork(node)
        \/ NodePassesToken(node)
        \/ DetectTermination
        \/ SendMessage(node)
        \/ NodeReceives(node)

TokenIsAccurate ==
    DetectTermination => Terminated

MyProperty ==
    /\ [][DetectTermination => Terminated]_vars

MustFinishProperty ==
    <>[](Terminated)

TerminationEventuallyDetected ==
    <>Terminated ~> TerminationDetected

TerminationDetectionIsCorrect ==
    TerminationDetected => Terminated

TerminationDetectionIsStable ==
    [][TerminationDetected => TerminationDetected']_TerminationDetected

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)



====
