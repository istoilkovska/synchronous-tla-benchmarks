------------------------------ MODULE floodmin ------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

VARIABLES state, msgs, round, phase,
      crash, failed, receivers
      
vars == <<state, msgs, round, phase, crash, failed, receivers>>

P == 1 .. N
unknown == 3 
V == {0, 1, 2}
K == 2

C == [ min : V, decision : {0, 1, 2, unknown}]
InitC == [ min : V, decision : {unknown}]

    
InitEnvironment ==
    /\ phase = "msgs"
    /\ round = 0
    /\ crash \in SUBSET(P)  
    /\ failed = {}
    /\ Cardinality(failed \cup crash) <= F
    /\ receivers \in [crash -> SUBSET(P)]
    
InitAlgorithm ==
    /\ state \in [P -> InitC]
    /\ msgs = [p \in P |-> [q \in P |-> unknown]] \* two-dimensional messages array
    
Min(S) == IF 0 \in S THEN 0 ELSE IF 1 \in S THEN 1 ELSE 2

Msgs(p) == IF p \in failed 
        THEN {}
        ELSE {v \in V : \E q \in P : msgs[q][p] # unknown /\ msgs[q][p] = v}
  
    
SendMessage(p, q) ==  
    state[p].min         

EnvSemMsg(m, p, q) ==
    IF \/ p \in failed 
       \/ p \in crash /\ q \notin receivers[p] 
    THEN unknown
    ELSE m
    
EnvSemState(p, s1, s2) == 
    IF p \in failed \/ p \in crash \/ s2.decision # unknown
    THEN s2 
    ELSE s1    

Update(s, X) == 
    LET m == Min(X) IN 
    LET d == IF round >= (T \div K) + 1
             THEN m
             ELSE unknown IN
    [min |-> m, decision |-> d]     

MsgsEnvironment ==
IF round <= T \div K 
THEN
    /\ phase' = "trans"
    /\ round' = round+1 
    /\ UNCHANGED <<crash, failed, receivers>>
ELSE UNCHANGED vars

TransEnvironment ==
    /\ phase' = "msgs"
    /\ failed' = failed \cup crash
    /\ crash' \in SUBSET(P \ failed')
    /\ Cardinality(failed' \cup crash') <= F
    /\ receivers' \in [crash' -> SUBSET(P)]
    /\ UNCHANGED round
    
MsgsAlgorithm ==
    IF round <= T \div K 
    THEN 
    /\ msgs' = [p \in P |-> [q \in P |-> EnvSemMsg(SendMessage(p, q), p, q)]]
    /\ UNCHANGED state                                         
    ELSE UNCHANGED vars    
    
TransAlgorithm ==
    /\ state' = [p \in P |-> EnvSemState(p, Update(state[p], Msgs(p)), state[p])]
    /\ msgs' = [p \in P |-> [q \in P |-> unknown]]      
    

\* next state action predicates

NextEnvironment ==
    \/ phase = "msgs" /\ MsgsEnvironment 
    \/ phase = "trans" /\ TransEnvironment

NextAlgorithm ==
    \/ phase = "msgs" /\ MsgsAlgorithm
    \/ phase = "trans" /\ TransAlgorithm
 
Init == InitAlgorithm /\ InitEnvironment          
Next == NextAlgorithm /\ NextEnvironment 

\* fairness constraint
Fairness == WF_vars(Next)

\* specification
Spec == Init /\ [][Next]_vars /\ Fairness
                 
\* safety properties 
Agreement == \E W \in SUBSET(V) : Cardinality(W) = K /\ [](\A q \in P : (q \notin failed /\ state[q].decision # unknown) => state[q].decision \in W)
Validity == \A I \in SUBSET(V) : I = {state[p].min : p \in P} => [](\A p \in P : (state[p].decision # unknown => state[p].decision \in I))

\* liveness property
Termination == <>(\A p \in P : p \in failed \/ state[p].decision # unknown) 



=============================================================================
\* Modification History
\* Last modified Thu Sep 28 18:11:32 CEST 2017 by stoilkov
\* Created Thu Sep 28 18:06:12 CEST 2017 by stoilkov
