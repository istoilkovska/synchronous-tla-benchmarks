-------------------------------- MODULE edac --------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

VARIABLES state, msgs, previous, round, phase,
      crash, failed, receivers
      
vars == <<state, previous, msgs, round, phase, crash, failed, receivers>>

P == 1 .. N \* set of processes
unknown == 2 
V == {0, 1}
M == {"W", "D"} \* message type
Messages == {"W"} \X (SUBSET(V) \ {{}}) \cup {"D"} \X V \cup {<<>>}

C == [ W : {{0}, {1}, {0, 1}},  halt : {FALSE}, decision : {0, 1, unknown}]
InitC == [ W : {{0}, {1}},  halt : {FALSE}, decision : {unknown}]

InitEnvironment ==
    /\ phase = "msgs"
    /\ round = 0
    /\ crash \in SUBSET(P)  
    /\ failed = {}
    /\ Cardinality(failed \cup crash) <= F
    /\ receivers \in [crash -> SUBSET(P)]
    
InitAlgorithm ==
    /\ state \in [P -> InitC]
    /\ msgs = [p \in P |-> [q \in P |-> <<>>]] \* two-dimensional messages array
    /\ previous = [p \in P |-> P]
    
NRcv(p) == {q \in P : msgs[q][p] = <<>>}

Msgs(p) == IF p \in failed
        THEN {}
        ELSE UNION {U \in SUBSET(V): \E q \in P : msgs[q][p] = <<"W", U>> }   
    
SendMessage(p, q) ==  
    IF state[p].decision # unknown
    THEN <<"D", state[p].decision>>
    ELSE <<"W", state[p].W>>

EnvSemMsg(m, p, q) ==
    IF \/ p \in failed
       \/ state[p].halt
       \/ (p \in crash /\ q \notin receivers[p])
    THEN <<>>
    ELSE m
         
EnvSemState(p, s1, s2) == 
    IF p \in failed \/ p \in crash \/ s2.halt
    THEN s2 
    ELSE s1             

Update(p, X) == 
    LET arrived == {x \in V : \E q \in P: msgs[q][p] = <<"D", x>>} IN
    LET w == state[p].W \cup Msgs(p) IN
    LET dec == IF arrived = {0}
               THEN 0
               ELSE IF arrived = {1}
                    THEN 1
                    ELSE IF previous[p] = NRcv(p) 
                         THEN IF 0 \in w
                              THEN 0 
                              ELSE 1
                         ELSE state[p].decision IN           
    LET h == state[p].decision # unknown IN
    [W |-> w, halt |-> h, decision |-> dec]         

MsgsEnvironment ==
IF \A p \in P \ failed : state[p].halt 
THEN UNCHANGED vars
ELSE
    /\ phase' = "trans"
    /\ round' = round+1 
    /\ UNCHANGED <<crash, failed, receivers>>

TransEnvironment ==
    /\ phase' = "msgs"
    /\ failed' = failed \cup crash
    /\ crash' \in SUBSET(P \ failed')
    /\ Cardinality(failed' \cup crash') <= F
    /\ receivers' \in [crash' -> SUBSET(P)]
    /\ UNCHANGED round
    
MsgsAlgorithm ==
IF \A p \in P \ failed : state[p].halt 
THEN UNCHANGED vars
ELSE
    /\ msgs' = [p \in P |-> [q \in P |-> EnvSemMsg(SendMessage(p, q), p, q)]]
    /\ UNCHANGED <<state, previous>>                                         
    
TransAlgorithm ==
    /\ state' = [p \in P |-> EnvSemState(p, Update(p, Msgs(p)), state[p])]
    /\ previous' = [p \in P |-> IF ~state[p].halt THEN NRcv(p) ELSE previous[p]]
    /\ msgs' = [p \in P |-> [q \in P |-> <<>>]]      
    

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
Agreement == [](\A p \in P : \A q \in P : (p \notin failed /\ state[p].decision # unknown /\ q \notin failed /\ state[q].decision # unknown => 
                                                  state[p].decision = state[q].decision)) 

\* liveness property
Termination == <>(\A p \in P : p \in failed \/ state[p].decision # unknown) 



=============================================================================
\* Modification History
\* Last modified Thu Sep 28 18:50:35 CEST 2017 by stoilkov
\* Created Thu Sep 28 18:35:23 CEST 2017 by stoilkov
