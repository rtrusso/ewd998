--------------------- MODULE A3 ---------------------

EXTENDS Integers
CONSTANT NumberOfNodes 

VARIABLE NodeWorking
VARIABLE TerminationDetected
VARIABLE Network

vars == << NodeWorking, TerminationDetected, Network >>

Nodes == 1..NumberOfNodes

TypeOk ==
    /\ Network \in [Nodes -> Nat]
    /\ NodeWorking \in [Nodes -> {TRUE, FALSE}]
    /\ TerminationDetected \in {TRUE, FALSE}

Terminated == 
    /\ \A node \in Nodes : NodeWorking[node] = FALSE
    /\ \A node \in Nodes : Network[node] = 0

Init ==
    /\ NodeWorking = [node \in Nodes |-> (node \div 2) * 2 = node ]
    /\ Network = [node \in Nodes |-> 0]
    /\ TerminationDetected = FALSE

NodeFinishesWork(node) ==
    /\ NodeWorking[node] = TRUE
    /\ Network[node] = 0
    /\ NodeWorking' = [NodeWorking EXCEPT ![node] = FALSE]
    /\ UNCHANGED Network
    /\ UNCHANGED TerminationDetected

NodePassesToken(node) == 
    /\ TRUE
    /\ UNCHANGED Network
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED NodeWorking

DetectTermination == 
    /\ TerminationDetected = FALSE
    /\ Terminated
    /\ TerminationDetected' = TRUE
    /\ UNCHANGED Network
    /\ UNCHANGED NodeWorking

SendMessage(sourceNode) ==
    \E destinationNode \in Nodes :
      /\ NodeWorking[sourceNode] = TRUE
      /\ Network' = [Network EXCEPT ![destinationNode] = @ + 1]
      /\ UNCHANGED NodeWorking
      /\ UNCHANGED TerminationDetected

NodeReceives(sourceNode) ==
    /\ Network[sourceNode] > 0
    /\ Network' = [Network EXCEPT ![sourceNode] = @ - 1]
    /\ NodeWorking' = [NodeWorking EXCEPT ![sourceNode] = TRUE]
    /\ UNCHANGED TerminationDetected

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
