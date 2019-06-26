--------------------- MODULE floodset_abstract_m1 ---------------------

EXTENDS Naturals, FiniteSets, TLC

VARIABLES loc1, locOther, msgs, phase, crash, decisionRound, receivers, someP, pclean

vars == <<loc1, locOther, msgs, phase, crash, decisionRound, receivers, someP, pclean>>

v0 == 0 \* default decision value
V == {0, 1} \* set of values
I == 1 .. 6 \* indices of process locations
U == 1 .. 7 \* message array indices (process locations + 2 concrete processes)
u1 == 7 \* index for process 1
Loc == [ W : {{0}, {1}, {0, 1}}, halt : BOOLEAN] \* possible process locations
AM == {W \in SUBSET(SUBSET(V)) : W = {} \/ Cardinality(W) = 1 \/ (Cardinality(W) = 2 /\ {} \in W)}  

\* translate index i \in I to location l \in Loc
location(i) ==
    LET x == i - 1 IN 
    LET w == IF x \div 2 = 0 THEN {0} ELSE IF x \div 2 = 1 THEN {1} ELSE {0, 1} IN
    LET h == IF x % 2 = 0 THEN FALSE ELSE TRUE IN
    [W |-> w, halt |-> h]

\* translate location l \in Loc to index i \in I    
index(l) ==
    LET f == IF l.halt = FALSE THEN 0 ELSE 1 IN
    LET w == IF l.W = {0} THEN 0 ELSE IF l.W = {1} THEN 1 ELSE 2 IN
    2 * w + f + 1
    
\* get value set, given index u \in U     
valueSet(u) ==
    IF u = u1
    THEN loc1.W
    ELSE location(u).W    

\* Set of indices witnessing non-failed processes     
IndexNonFailed == {u1} \cup {index(l) : l \in {l1 \in locOther : ~l1.halt}}
\* Set of locations of active processes
Active == {loc1} \cup locOther 
\* Set of indices of correct processes (i.e., non-failed and non-crashed) 
Correct == {u1} \cup {index(l) : l \in {l1 \in locOther : ~l1.halt /\ crash[l1] # {TRUE}}}    

\* set failure flag of l to TRUE  
failedLocation(l) ==
    [W |-> l.W, halt |-> TRUE]
 
\* Set of initial locations         
InitActive == {[W |-> {0}, halt |-> FALSE], 
               [W |-> {1}, halt |-> FALSE]}   
               
\* type invariant
TypeOK ==
    /\ loc1 \in Loc
    /\ locOther \in SUBSET(Loc)
    /\ msgs \in [IndexNonFailed -> [IndexNonFailed -> AM]]
    /\ phase \in {"msgs", "trans"}
    /\ crash \in [{l \in locOther : ~l.halt} -> SUBSET(BOOLEAN)]
    /\ pclean \in BOOLEAN
    /\ decisionRound \in BOOLEAN    
    /\ receivers \in [{l \in DOMAIN crash : TRUE \in crash[l]} \X {u \in Correct : Cardinality(valueSet(u)) = 1} -> SUBSET(BOOLEAN)]
    /\ someP \in [{l \in locOther : ~l.halt /\ Cardinality(l.W) = 1 /\ crash[l] # {TRUE}} -> BOOLEAN]

\* initial predicate of the environment        
InitEnvironment == 
    /\ phase = "msgs" \* current phase of the algorithm
    /\ decisionRound = FALSE \* is the current round the decision round, after a clean round has occurred
    /\ crash \in [locOther -> ((SUBSET(BOOLEAN)) \ {{}})] \* crash array 
    /\ pclean = FALSE \* predicate for the clean round
    /\ receivers \in [{l \in DOMAIN crash : TRUE \in crash[l]} \X Correct -> ((SUBSET(BOOLEAN)) \ {{}})] \* receivers array 
    /\ someP = [l \in {k \in locOther : crash[k] # {TRUE}} |-> FALSE]
    
\* initial predicate of the algorithm      
InitAlgorithm ==
    /\ loc1 \in InitActive \* first fixed process
    /\ locOther \in ((SUBSET(InitActive)) \ {{}}) \* set of witnesses for the other N - 2 processes
    /\ msgs = [u \in IndexNonFailed |-> [v \in IndexNonFailed |-> {{}}]]  \* two-dimensional messages array

\* environment transition in the message exchage phase  
MsgsEnvironment ==
    /\ phase' =  "trans" 
    /\ pclean' = IF \A l \in DOMAIN crash : TRUE \notin crash[l] THEN TRUE ELSE pclean
    /\ decisionRound' \in IF pclean' THEN {TRUE, FALSE} ELSE {FALSE}
    /\ someP' \in [{l \in locOther : ~l.halt /\ Cardinality(l.W) = 1 /\ crash[l] # {TRUE}} -> BOOLEAN]
    /\ UNCHANGED <<crash, receivers>>

\* environment transition in the state update phase
TransEnvironment ==
    /\ phase' =  "msgs"
    /\ crash' \in [{l \in locOther' : ~l.halt} -> ((SUBSET(BOOLEAN)) \ {{}})]
    /\ receivers' \in [{l \in DOMAIN crash' : TRUE \in crash[l]'} \X {u \in Correct' : Cardinality(valueSet(u)') = 1} -> ((SUBSET(BOOLEAN)) \ {{}})]
    /\ someP' = [l \in {l \in locOther : ~l.halt /\ Cardinality(l.W) = 1 /\ crash[l] # {TRUE}}' |-> FALSE]
    /\ UNCHANGED <<decisionRound, pclean>>
 
\* message generation function of a correct process    
SendMessage(u, v) ==
    valueSet(u)     

\* update function of a correct process 
\* (that received the same messages as the abstract location that witnesses it) 
Update(l, u) ==
    LET x == IF \/ /\ l.W = {0} 
                   /\ \E m \in {{1}, {0, 1}} : \E v \in IndexNonFailed : m \in msgs[v][u]  
                \/ /\ l.W = {1}
                   /\ \E m \in {{0}, {0, 1}} : \E v \in IndexNonFailed : m \in msgs[v][u]
             THEN {0, 1}
             ELSE l.W IN
    LET w == IF decisionRound
             THEN IF x = {0}
                  THEN {0}
                  ELSE IF x = {1}
                       THEN {1}
                       ELSE {v0}
             ELSE x IN
    LET h == IF decisionRound 
             THEN TRUE
             ELSE FALSE IN
    [W |-> w, halt |-> h]  

\* update function of a correct process 
\* (that received messages different from the ones received by abstract location that witnesses it)
UpdateOther(l, X) ==
    LET w == IF decisionRound
             THEN IF l.W \cup X = {0}
                  THEN {0}
                  ELSE IF l.W \cup X = {1}
                       THEN {1}
                       ELSE {v0}
             ELSE l.W \cup X IN
    LET h == IF decisionRound 
             THEN TRUE
             ELSE FALSE IN
    [W |-> w, halt |-> h]  

\* update of a process location witnessing correct processes
UpdateCorrect(l, u) == 
    IF Cardinality(l.W) = 1 /\ loc1.W = l.W
    THEN IF \A v \in IndexNonFailed : v \notin {u1} /\ location(v).W # l.W => crash[location(v)] = {TRUE} /\ receivers[location(v), u] = {FALSE}
         THEN {UpdateOther(l, l.W)}
         ELSE IF someP[l]
              THEN {Update(l, u), UpdateOther(l, l.W)}
              ELSE {Update(l, u)}
    ELSE {Update(l, u)}  

\* delivery of messages by the environment       
EnvSemMsg(m, u, v) ==
    IF u \in {u1}   
    THEN {m}
    ELSE LET l == location(u) IN
         IF crash[l] = {TRUE, FALSE}
         THEN IF Cardinality(valueSet(v)) = 1 /\ (v \in {u1} \/ crash[location(v)] # {TRUE})  
              THEN IF receivers[l,v] = {TRUE}
                   THEN {m}
                   ELSE {{}, m}
              ELSE {{}}                   
         ELSE IF crash[l] = {TRUE} 
              THEN IF Cardinality(valueSet(v)) = 1 /\ (v \in {u1} \/ crash[location(v)] # {TRUE})
                   THEN IF receivers[l,v] = {TRUE}
                        THEN {m}
                        ELSE IF receivers[l,v] = {FALSE}
                             THEN {{}}
                             ELSE {{}, m}
                   ELSE {{}}          
              ELSE IF Cardinality(valueSet(v)) = 1 /\ (v \in {u1} \/ crash[location(v)] # {TRUE})
                   THEN {m}
                   ELSE {{}}

\* state update of the fixed processes w.r.t. the environment  
EnvSemState(l, u) ==
    IF l.halt
    THEN l
    ELSE Update(l, u)

\* state update of the other processes w.r.t. the environment
EnvSemStateOther(l) ==
    IF l.halt
    THEN {l}
    ELSE IF crash[l] = {TRUE}
         THEN {failedLocation(l)}  \* all processes witnessed by l crashed 
         ELSE IF crash[l] = {TRUE, FALSE} \* some processes witnessed by l crashed, and some not
              THEN  UpdateCorrect(l, index(l)) \cup {failedLocation(l)} 
              ELSE  UpdateCorrect(l, index(l)) \* no processes witnessed by l crashed

\* algorithm transition in the message exchange phase
MsgsAlgorithm == 
    /\ msgs' = [u \in IndexNonFailed |-> [v \in IndexNonFailed |-> EnvSemMsg(SendMessage(u, v), u, v)]]
    /\ UNCHANGED <<loc1, locOther>> 

\* algorithm transition in the state update phase    
TransAlgorithm ==
    /\ loc1' = EnvSemState(loc1, u1)
    /\ locOther' = UNION{EnvSemStateOther(l) : l \in locOther}  
    /\ msgs' = [u \in IndexNonFailed' |-> [v \in IndexNonFailed' |-> {{}}]]
    
NextEnvironment == 
    \/ phase = "msgs" /\ MsgsEnvironment
    \/ phase = "trans" /\ TransEnvironment
    
NextAlgorithm == 
    \/ phase = "msgs" /\ MsgsAlgorithm 
    \/ phase = "trans" /\ TransAlgorithm 
    
Init == InitAlgorithm /\ InitEnvironment    
    
Next == NextAlgorithm /\ NextEnvironment   

\* constraints    
Fairness == 
    /\ WF_vars(Next)
    /\ <>[](\A l \in DOMAIN crash : TRUE \notin crash[l])
    /\ <>decisionRound

\* specification    
Spec == Init /\ [][Next]_vars /\ Fairness

\* safety properties
Validity0 == ((\A l \in Active : l.W = {0}) => 
                            [](loc1.halt => loc1.W = {0}))
Validity1 == ((\A l \in Active : l.W = {1}) => 
                            [](loc1.halt => loc1.W = {1}))
\* Validity: if all processes start with the same value, then this is the only 
\*           possible decision value
Validity == Validity0 /\ Validity1

\* liveness property
\* Termination: all correct processes eventually decide
Termination == <>(loc1.halt)

=============================================================================
\* Modification History
\* Last modified Fri Oct 13 17:17:15 CEST 2017 by stoilkov
\* Created Fri Sep 22 14:29:20 CEST 2017 by stoilkov
