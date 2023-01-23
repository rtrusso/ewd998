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

VarsWithoutTokenOwner == << TerminationDetected, Network, NodeWorking, NodeMessageCounter, NodeColor, TokenColor, TokenCounter >>

ATD == INSTANCE A3
Nodes == ATD!Nodes
Colors == { "Purple", "Green" }

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
    /\ NodeColor = [node \in Nodes |-> "Purple"]
    /\ TokenColor = "Purple"
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
    /\ TokenCounter' = TokenCounter + NodeMessageCounter[node]
    /\ TokenColor' = IF NodeColor[node] = "Green" THEN "Green" ELSE TokenColor
    /\ NodeColor' = [NodeColor EXCEPT ![node] = "Purple"]
    /\ UNCHANGED Network
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED NodeMessageCounter

DetectTermination == 
    /\ TokenOwner = NumberOfNodes+1
    /\ TokenColor = "Purple"
    /\ TokenCounter = 0

UpdateTerminationDetected ==
    /\ TerminationDetected = FALSE
    /\ DetectTermination
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
    /\ NodeColor' = [NodeColor EXCEPT ![sourceNode] = "Green"]
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED TokenOwner
    /\ UNCHANGED << TokenColor, TokenCounter >>

InitiateNewRound ==
    /\ TokenOwner = NumberOfNodes+1
    /\ (TokenColor = "Green" \/ TokenCounter # 0)
    /\ TokenOwner' = 1
    /\ TokenColor' = "Purple"
    /\ TokenCounter' = 0
    /\ NodeColor' = [NodeColor EXCEPT ![1] = "Purple"]
    /\ UNCHANGED << Network, TerminationDetected >>
    /\ UNCHANGED << NodeWorking, NodeMessageCounter >>
    \* /\ UNCHANGED << TokenCounter >>

Next ==
    \E node \in ATD!Nodes :
        \/ NodeFinishesWork(node)
        \/ NodePassesToken(node)
        \/ SendMessage(node)
        \/ NodeReceives(node)
        \/ UpdateTerminationDetected
        \/ InitiateNewRound


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

(** Try to find a trace that causes some condition to happen - this 
will 'fail' and show the state trace **)
VerifyThatTokenCanBePastANodeThatReceivesAMessage ==
    [][~(
        /\ NodeMessageCounter[3] = 2
        /\ NodeMessageCounter'[3] = 1
        /\ TokenOwner = 3
    )]_vars

MyAlias == [
    ATDTerminated |-> ATD!Terminated,
    NextEnabled |-> ENABLED(Next),
    SendMessageEnabled |-> [
        node \in Nodes|-> ENABLED(SendMessage(node))
    ]
]


(**
temporal forumla - must specify multiple states using always[] or eventually<> operators, leads-to
action formula - must have primed variables

<>X == ~[]~X

**)

====