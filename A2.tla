--------------------- MODULE A2 ---------------------

EXTENDS Integers
CONSTANT NumberOfNodes 

VARIABLE NodeWorking
VARIABLE Token

vars == <<NodeWorking, Token>>

Nodes == 1..NumberOfNodes

Terminated == \A node \in Nodes : NodeWorking[node] = FALSE
TokenIsValid == 
    \/ Token \in DOMAIN Nodes
    \/ Token = NumberOfNodes+1

\* Codomain(function) = { domainItem \in DOMAIN(function) : function[domainItem] }

Init ==
    /\ NodeWorking = [node \in Nodes |-> TRUE]
    /\ Token = 1

NodeFinishesWork(node) ==
    \* /\ NodeWorking' = node :> FALSE @@ NodeWorking
    /\ NodeWorking' = [NodeWorking EXCEPT ![node] = FALSE]
    /\ UNCHANGED Token

NodePassesToken(node) ==
    /\ Token = node
    /\ Token' = node+1
    /\ NodeWorking[node] = FALSE
    /\ UNCHANGED NodeWorking

DetectTermination == 
    /\ Token = NumberOfNodes + 1
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED Token

Next ==
    \E node \in Nodes :
        \/ NodeFinishesWork(node)
        \/ NodePassesToken(node)
        \/ DetectTermination

TokenIsAccurate ==
    /\ DetectTermination
    /\ Terminated

MyProperty ==
    /\ [][DetectTermination => Terminated]_vars

====
