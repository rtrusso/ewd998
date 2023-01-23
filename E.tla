---- MODULE E ----

EXTENDS Integers, TLC
CONSTANT NumberOfNodes

VARIABLE
    TerminationDetected,
    Network,
    NodeWorking,
    NodeMessageCounter,
    Token

vars == << TerminationDetected, Network, NodeWorking, Token, NodeMessageCounter >>

ATD == INSTANCE A3

TypeOk ==
    /\ Token \in Nat
    /\ Token > 0
    /\ Token <= NumberOfNodes+1
    /\ ATD!TypeOk
    /\ NodeMessageCounter \in [ATD!Nodes -> Int]

Init ==
    /\ NodeWorking = [node \in ATD!Nodes |-> (node \div 2) * 2 = node ]
    /\ Network = [node \in ATD!Nodes |-> 0]
    /\ TerminationDetected = FALSE
    /\ Token = 1
    /\ NodeMessageCounter = [node \in ATD!Nodes |-> 0]

NodeFinishesWork(node) ==
    /\ NodeWorking[node] = TRUE
    /\ Network[node] = 0
    /\ NodeWorking' = [NodeWorking EXCEPT ![node] = FALSE]
    /\ UNCHANGED Network
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED Token
    /\ UNCHANGED NodeMessageCounter

NodePassesToken(node) == 
    /\ Token = node
    /\ NodeWorking[node] = FALSE
    /\ Token' = Token + 1
    /\ UNCHANGED Network
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED NodeMessageCounter

UpdateTerminationDetected ==
    /\ TerminationDetected = FALSE
    /\ Token = NumberOfNodes + 1
    /\ TerminationDetected' = TRUE
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED Network
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED Token
    /\ UNCHANGED NodeMessageCounter

SendMessage(sourceNode) ==
    \E destinationNode \in ATD!Nodes :
      /\ NodeWorking[sourceNode] = TRUE
      /\ Network' = [Network EXCEPT ![destinationNode] = @ + 1]
      /\ NodeMessageCounter' = [NodeMessageCounter EXCEPT ![sourceNode] = @ + 1]
      /\ UNCHANGED NodeWorking
      /\ UNCHANGED TerminationDetected
      /\ UNCHANGED Token

NodeReceives(sourceNode) ==
    /\ Network[sourceNode] > 0
    /\ Network' = [Network EXCEPT ![sourceNode] = @ - 1]
    /\ NodeWorking' = [NodeWorking EXCEPT ![sourceNode] = TRUE]
    /\ NodeMessageCounter' = [NodeMessageCounter EXCEPT ![sourceNode] = @ - 1]
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED Token

DetectTermination == 
    /\ Token = NumberOfNodes+1
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED Network
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED Token
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED NodeMessageCounter

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
    [][DetectTermination => Terminated]_vars

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