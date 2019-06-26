-------------------------------- MODULE nbac --------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES state, msgs, round, phase, crash, receivers

vars == <<state, msgs, round, phase, crash, receivers>>

P == 1..N
O == 3..N
unknown == 2
v0 == 0
V == {0, 1}
C == [W : {{0}, {1}, {0, 1}}, decision : {0, 1, unknown}]
InitC == [W : {{0}, {1}}, decision : {unknown}]

InitEnvironment ==
    /\ phase = "msgs_nbac"
    /\ round = 0
    /\ crash \in SUBSET(O) 
    /\ Cardinality(crash) <= F
    /\ receivers \in [crash -> SUBSET(P)]
    
InitAlgorithm ==
    /\ state \in [P -> InitC]
    /\ msgs = [p \in P |-> [q \in P |-> {}]]
    
EnvSemMsg(m, p, q) ==
    IF \/ p \in crash /\ p \notin DOMAIN receivers
       \/ p \in crash /\ q \notin receivers[p]
    THEN {}
    ELSE m    
    
SendMessage(p) ==
    state[p].W
    
EnvSemStateNBAC(p) == 
    IF p \in crash
    THEN state[p]
    ELSE IF \A q \in P : msgs[q][p] # {} /\ msgs[q][p] = {1}
         THEN [W |-> {1}, decision |-> unknown]
         ELSE [W |-> {0}, decision |-> unknown]

Msgs(p) ==
    IF p \in crash
    THEN {}
    ELSE UNION{m \in SUBSET(V) : \E q \in P : msgs[q][p] = m}

Update(s, M) ==
    LET w == s.W \cup M IN
    LET d == IF round = T + 1
             THEN IF w = {0}
                  THEN 0
                  ELSE IF w = {1}   
                       THEN 1 
                       ELSE v0
             ELSE unknown IN
    [W |-> w, decision |-> d]
                  
         
EnvSemStateConsensus(p, s1, s2) ==
    IF p \in crash
    THEN s2
    ELSE s1         
    
MsgsEnvironment ==
IF round <= T
THEN
    /\ \/ /\ phase = "msgs_nbac" 
          /\ phase' = "trans_nbac"
          /\ UNCHANGED round
       \/ /\ phase = "msgs" 
          /\ phase' = "trans"
          /\ round' = round + 1
    /\ UNCHANGED <<crash, receivers>>
ELSE UNCHANGED vars    
    
TransEnvironment == 
    /\ phase' = "msgs"
    /\ crash' \in SUBSET(O)
    /\ crash \subseteq crash'
    /\ Cardinality(crash') <= F
    /\ receivers' \in [crash' \ crash -> SUBSET(P)]  
    /\ UNCHANGED round       
    
MsgsNBAC ==
    /\ msgs' = [p \in P |-> [q \in P |-> EnvSemMsg(SendMessage(p), p, q)]]
    /\ UNCHANGED state   

TransNBAC ==
    /\ state' = [p \in P |-> EnvSemStateNBAC(p)]
    /\ msgs' = [p \in P |-> [q \in P |-> {}]]
    
MsgsConsensus ==
IF round <= T
THEN
    /\ msgs' = [p \in P |-> [q \in P |-> EnvSemMsg(SendMessage(p), p, q)]]
    /\ UNCHANGED state
ELSE UNCHANGED vars    
    
TransConsensus ==
    /\ state' = [p \in P |-> EnvSemStateConsensus(p, Update(state[p], Msgs(p)), state[p])]
    /\ msgs' = [p \in P |-> [q \in P |-> {}]] 
    
NextEnvironment ==
    \/ phase = "msgs_nbac" /\ MsgsEnvironment    
    \/ phase = "trans_nbac" /\ TransEnvironment
    \/ phase = "msgs" /\ MsgsEnvironment    
    \/ phase = "trans" /\ TransEnvironment    
    
NextAlgorithm ==
    \/ phase = "msgs_nbac" /\ MsgsNBAC    
    \/ phase = "trans_nbac" /\ TransNBAC
    \/ phase = "msgs" /\ MsgsConsensus    
    \/ phase = "trans" /\ TransConsensus
    
Init == InitAlgorithm /\ InitEnvironment
Next == NextAlgorithm /\ NextEnvironment    
    
Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

Agreement ==
    [](\A p \in P : \A q \in P : p \notin crash /\ q \notin crash /\ state[p].decision # unknown /\ state[q].decision # unknown => 
                                 state[p].decision = state[q].decision)
                                 
Justification ==
    ([](\A p \in P : state[p].decision # unknown => state[p].decision = 1)) 
        => (\A p \in P : state[p].W = {1})
        
Obligation ==
    (\A p \in P : state[p].W = {1}) /\ crash = {} => [](\A p \in P : state[p].decision # unknown => state[p].decision = 1) 

Termination == 
    <>(\A p \in P : p \in crash \/ state[p].decision # unknown)


    
=============================================================================
\* Modification History
\* Last modified Fri Aug 18 17:40:56 CEST 2017 by ilina
\* Created Thu Aug 17 19:43:16 CEST 2017 by ilina
