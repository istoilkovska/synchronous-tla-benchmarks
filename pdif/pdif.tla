-------------------------------- MODULE pdif --------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

VARIABLES state, msgs, nb, round, phase,
      crash, failed, receivers
      
vars == <<state, nb, msgs, round, phase, crash, failed, receivers>>

P == 1 .. N \* set of processes
unknown == 2 
V == {0, 1}
Messages == BOOLEAN \times V

C == [ est : V, halt : BOOLEAN, early : BOOLEAN ]
InitC == [ est : V, halt : {FALSE}, early : {FALSE} ]

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
    /\ nb = [p \in P |-> N]
    
Rcv(p) == {q \in P : msgs[q][p] # <<>>} 
    
SendMessage(p, q) ==  
    <<state[p].early, state[p].est>>

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

Update(p) == 
    LET decide == \E m \in V : \E q \in P : msgs[q][p] = <<TRUE, m>> IN 
    LET e == IF state[p].est = 1 /\ \E d \in BOOLEAN : \E q \in P : msgs[q][p] = <<d, 0>> 
             THEN 0
             ELSE state[p].est IN
    LET h == IF state[p].early \/ round >= T + 1 
             THEN TRUE
             ELSE FALSE IN
    LET d == IF decide \/ nb[p] = Cardinality(Rcv(p)) 
             THEN TRUE 
             ELSE FALSE IN             
    [est |-> e, halt |-> h, early |-> d]

MsgsEnvironment ==
IF round > T 
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
IF round > T 
THEN UNCHANGED vars
ELSE
    /\ msgs' = [p \in P |-> [q \in P |-> EnvSemMsg(SendMessage(p, q), p, q)]]
    /\ UNCHANGED <<state, nb>>                                         
    
TransAlgorithm ==
    /\ state' = [p \in P |-> EnvSemState(p, Update(p), state[p])]
    /\ nb' = [p \in P |-> IF ~state[p].halt THEN Cardinality(Rcv(p)) ELSE nb[p]]
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
Validity == \A v \in V : (\A p \in P : state[p].est = v) => [](\A q \in P : (q \notin failed /\ state[q].halt) => state[q].est = v)
Agreement == [](\A p \in P : \A q \in P : (state[p].halt /\ state[q].halt => 
                                                  state[p].est = state[q].est)) 

\* liveness property
Termination == <>(\A p \in P : p \in failed \/ state[p].halt) 


=============================================================================
\* Modification History
\* Last modified Thu Sep 28 19:24:55 CEST 2017 by stoilkov
\* Created Thu Sep 28 18:58:45 CEST 2017 by stoilkov
