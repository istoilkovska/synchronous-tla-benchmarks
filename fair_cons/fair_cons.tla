----------------------------- MODULE fair_cons -----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

VARIABLES state, msgs, round, phase,
      crash, failed, receivers
      
vars == <<state, msgs, round, phase, crash, failed, receivers>>

P == 1 .. N
unknown == 2 
V == {0, 1}
v0 == 0

C == [ est : V, prev_est : V \cup {unknown}, decided : BOOLEAN]
InitC == [ est : V, prev_est : {unknown}, decided : {FALSE}]

    
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

Msgs(p) == IF p \in failed 
           THEN {}
           ELSE {m \in V : \E q \in P : msgs[q][p] = m} 
           
Min(S) == IF 0 \in S THEN 0 ELSE 1            
    
SendMessage(p, q) ==  
    IF state[p].est # state[p].prev_est
    THEN state[p].est
    ELSE unknown         

EnvSemMsg(m, p, q) ==
    IF \/ p \in failed 
       \/ p \in crash /\ q \notin receivers[p] 
    THEN unknown
    ELSE m
    
EnvSemState(p, s1, s2) == 
    IF p \in failed \/ p \in crash 
    THEN s2 
    ELSE s1    

Update(s, X) == 
    LET e == Min({s.est} \cup X) IN
    LET d == IF round >= T + 1
             THEN TRUE 
             ELSE FALSE IN 
    [est |-> e, prev_est |-> s.est, decided |-> d]     


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
Validity == \A v \in V : (\A p \in P : state[p].est = v) => [](\A q \in P : (q \notin failed /\ state[q].decided) => state[q].est = v)

Agreement == [](\A p \in P : \A q \in P : (state[p].decided /\ state[q].decided => state[p].est = state[q].est)) 

\* liveness property
Termination == <>(\A p \in P : p \in failed \/ state[p].decided) 
=============================================================================
\* Modification History
\* Last modified Fri Sep 29 11:55:55 CEST 2017 by stoilkov
\* Created Thu Sep 28 19:27:32 CEST 2017 by stoilkov
