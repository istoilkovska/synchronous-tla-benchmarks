------------------------------ MODULE floodset ------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

VARIABLES state, msgs, round, phase,
      crash, failed, receivers
      
vars == <<state, msgs, round, phase, crash, failed, receivers>>

P == 1 .. N
unknown == 2 
V == {0, 1}
v0 == 0

C == [ W : {{0}, {1}, {0, 1}}, decision : {0, 1, unknown}]
InitC == [ W : {{0}, {1}}, decision : {unknown}]

    
InitEnvironment ==
    /\ phase = "msgs"
    /\ round = 0
    /\ crash \in SUBSET(P)  
    /\ failed = {}
    /\ Cardinality(failed \cup crash) <= F
    /\ receivers \in [crash -> SUBSET(P)]
    
InitAlgorithm ==
    /\ state \in [P -> InitC]
    /\ msgs = [p \in P |-> [q \in P |-> {}]] \* two-dimensional messages array
    
Msgs(p) == IF p \in failed 
           THEN {}
           ELSE UNION{m \in SUBSET(V) : \E q \in P : msgs[q][p] = m}  
    
SendMessage(p, q) ==  
    state[p].W         

EnvSemMsg(m, p, q) ==
    IF \/ p \in failed 
       \/ p \in crash /\ q \notin receivers[p] 
    THEN {}
    ELSE m
    
EnvSemState(p, s1, s2) == 
    IF p \in failed \/ p \in crash \/ s2.decision # unknown
    THEN s2 
    ELSE s1    

Update(s, X) == 
    LET w == (s.W \cup X) IN 
    LET d == IF round >= T + 1
             THEN IF w = {0}
                  THEN 0
                  ELSE IF w = {1}
                       THEN 1
                       ELSE v0
             ELSE unknown IN
    [W |-> w, decision |-> d]     


MsgsEnvironment ==
IF round <= T 
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
    IF round <= T 
    THEN 
    /\ msgs' = [p \in P |-> [q \in P |-> EnvSemMsg(SendMessage(p, q), p, q)]]
    /\ UNCHANGED state                                         
    ELSE UNCHANGED vars    
    
TransAlgorithm ==
    /\ state' = [p \in P |-> EnvSemState(p, Update(state[p], Msgs(p)), state[p])]
    /\ msgs' = [p \in P |-> [q \in P |-> {}]]      
    

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
Validity == \A v \in V : (\A p \in P : state[p].W = {v}) => [](\A q \in P : (q \notin failed /\ state[q].decision # unknown) => state[q].decision = v)

Agreement == [](\A p \in P : \A q \in P : (state[p].decision # unknown /\ state[q].decision # unknown => state[p].decision = state[q].decision)) 

\* liveness property
Termination == <>(\A p \in P : p \in failed \/ state[p].decision # unknown) 

=============================================================================
\* Modification History
\* Last modified Thu Sep 28 18:12:11 CEST 2017 by stoilkov
\* Created Thu Apr 20 10:58:48 CEST 2017 by stoilkov
 
