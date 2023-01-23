---- MODULE E ----

EXTENDS Integers, TLC
CONSTANT NumberOfNodes

VARIABLE
    TerminationDetected,
    Network,
    NodeWorking,
    NodeMessageCounter,
    NodeColor,
    TokenColor,
    TokenCounter,
    TokenOwner

vars == << TerminationDetected, Network, NodeWorking, TokenOwner, NodeMessageCounter, NodeColor, TokenColor, TokenCounter >>

ATD == INSTANCE A3
Nodes == ATD!Nodes
Colors == { "Pink", "Green" }

TypeOk ==
    /\ TokenOwner \in Nat
    /\ TokenOwner > 0
    /\ TokenOwner <= NumberOfNodes+1
    /\ ATD!TypeOk
    /\ NodeMessageCounter \in [Nodes -> Int]
    /\ NodeColor \in [Nodes -> Colors]
    /\ TokenColor \in Colors
    /\ TokenCounter \in Int

Init ==
    /\ NodeWorking = [node \in ATD!Nodes |-> (node \div 2) * 2 = node ]
    /\ Network = [node \in ATD!Nodes |-> 0]
    /\ TerminationDetected = FALSE
    /\ TokenOwner = 1
    /\ NodeMessageCounter = [node \in ATD!Nodes |-> 0]
    /\ NodeColor = [node \in Nodes |-> "Pink"]
    /\ TokenColor = "Pink"
    /\ TokenCounter = 0

NodeFinishesWork(node) ==
    /\ NodeWorking[node] = TRUE
    /\ Network[node] = 0
    /\ NodeWorking' = [NodeWorking EXCEPT ![node] = FALSE]
    /\ UNCHANGED Network
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED TokenOwner
    /\ UNCHANGED NodeMessageCounter
    /\ UNCHANGED << NodeColor, TokenColor, TokenCounter >>

NodePassesToken(node) == 
    /\ TokenOwner = node
    /\ NodeWorking[node] = FALSE
    /\ TokenOwner' = TokenOwner + 1
    /\ UNCHANGED Network
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED NodeMessageCounter
    /\ UNCHANGED << NodeColor, TokenColor, TokenCounter >>

UpdateTerminationDetected ==
    /\ TerminationDetected = FALSE
    /\ TokenOwner = NumberOfNodes + 1
    /\ TerminationDetected' = TRUE
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED Network
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED TokenOwner
    /\ UNCHANGED NodeMessageCounter
    /\ UNCHANGED << NodeColor, TokenColor, TokenCounter >>

SendMessage(sourceNode) ==
    \E destinationNode \in ATD!Nodes :
      /\ NodeWorking[sourceNode] = TRUE
      /\ Network' = [Network EXCEPT ![destinationNode] = @ + 1]
      /\ NodeMessageCounter' = [NodeMessageCounter EXCEPT ![sourceNode] = @ + 1]
      /\ UNCHANGED NodeWorking
      /\ UNCHANGED TerminationDetected
      /\ UNCHANGED TokenOwner
      /\ UNCHANGED << NodeColor, TokenColor, TokenCounter >>

NodeReceives(sourceNode) ==
    /\ Network[sourceNode] > 0
    /\ Network' = [Network EXCEPT ![sourceNode] = @ - 1]
    /\ NodeWorking' = [NodeWorking EXCEPT ![sourceNode] = TRUE]
    /\ NodeMessageCounter' = [NodeMessageCounter EXCEPT ![sourceNode] = @ - 1]
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED TokenOwner
    /\ UNCHANGED << NodeColor, TokenColor, TokenCounter >>

DetectTermination == 
    /\ TokenOwner = NumberOfNodes+1
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED Network
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED TokenOwner
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED NodeMessageCounter
    /\ UNCHANGED << NodeColor, TokenColor, TokenCounter >>

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