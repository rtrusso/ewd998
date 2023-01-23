---- MODULE E ----

EXTENDS Integers, TLC
CONSTANT NumberOfNodes
CONSTANT TotalWork

VARIABLE
    TerminationDetected,
    Network,
    NodeWorking,
    (* WorkItemsDone, *)
    Token

vars == << TerminationDetected, Network, NodeWorking, (* WorkItemsDone,*) Token >>

ATD == INSTANCE A3

TypeOk ==
    /\ Token \in Nat
    /\ Token > 0
    /\ Token <= NumberOfNodes+1
    /\ ATD!TypeOk

NodeFinishesWork(node) ==
    /\ NodeWorking[node] = TRUE
    /\ Network[node] = 0
    /\ NodeWorking' = [NodeWorking EXCEPT ![node] = FALSE]
    /\ UNCHANGED Network
    /\ UNCHANGED TerminationDetected
    (* /\ UNCHANGED WorkItemsDone *)
    /\ UNCHANGED Token

NodePassesToken(node) == 
    /\ Token = node
    /\ NodeWorking[node] = FALSE
    /\ Token' = Token + 1
    /\ UNCHANGED Network
    /\ UNCHANGED NodeWorking
    (* /\ UNCHANGED WorkItemsDone *)
    /\ UNCHANGED TerminationDetected

UpdateTerminationDetected ==
    /\ TerminationDetected = FALSE
    /\ Token = NumberOfNodes + 1
    /\ TerminationDetected' = TRUE
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED Network
    /\ UNCHANGED NodeWorking
    (* /\ UNCHANGED WorkItemsDone *)
    /\ UNCHANGED Token


SendMessage(sourceNode) ==
    \E destinationNode \in ATD!Nodes :
      /\ NodeWorking[sourceNode] = TRUE
      /\ Network' = [Network EXCEPT ![destinationNode] = @ + 1]
      (* /\ WorkItemsDone' = WorkItemsDone + 1 *)
      \* /\ WorkItemsDone < TotalWork
      /\ UNCHANGED NodeWorking
      /\ UNCHANGED TerminationDetected
      /\ UNCHANGED Token

NodeReceives(sourceNode) ==
    /\ Network[sourceNode] > 0
    /\ Network' = [Network EXCEPT ![sourceNode] = @ - 1]
    /\ NodeWorking' = [NodeWorking EXCEPT ![sourceNode] = TRUE]
    /\ UNCHANGED TerminationDetected
    (* /\ UNCHANGED WorkItemsDone *)
    /\ UNCHANGED Token

DetectTermination == 
    /\ Token = NumberOfNodes+1
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED Network
    /\ UNCHANGED NodeWorking
    (* /\ UNCHANGED WorkItemsDone *)
    /\ UNCHANGED Token
    /\ UNCHANGED TerminationDetected

Init ==
    /\ NodeWorking = [node \in ATD!Nodes |-> (node \div 2) * 2 = node ]
    /\ Network = [node \in ATD!Nodes |-> 0]
    /\ TerminationDetected = FALSE
    (* /\ WorkItemsDone = 0 *)
    /\ Token = 1

Next ==
    \E node \in ATD!Nodes :
        \/ NodeFinishesWork(node)
        \/ NodePassesToken(node)
        \/ DetectTermination
        \/ UpdateTerminationDetected
        \/ SendMessage(node)
        \/ NodeReceives(node)


Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

THEOREM Spec => ATD!Spec

ATDSpec == ATD!Spec

Correct ==
    /\ [](ATD!TypeOk)
    /\ [](TypeOk)
    /\ ATD!TerminationEventuallyDetected

Terminated == 
    /\ \A node \in ATD!Nodes : NodeWorking[node] = FALSE
    /\ \A node \in ATD!Nodes : Network[node] = 0


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

NetworkIsFinite ==
    \A node \in ATD!Nodes : Network[node] <= 3


====