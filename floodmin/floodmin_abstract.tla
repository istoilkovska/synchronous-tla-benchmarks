------------------------- MODULE floodmin_abstract -------------------------

EXTENDS Naturals, FiniteSets, TLC

VARIABLES loc1, loc2, loc3, locOther, msgs, phase, crash, pclean, decisionRound, receivers, someP

vars == <<loc1, loc2, loc3, locOther, msgs, phase, crash, pclean, decisionRound, receivers, someP>>

unknown == 3 \* unknown decision value
V == {0, 1, 2} \* set of values
K == 2 \* cardinality of set of decision values
I == 1 .. 6 \* indices corresponding to process locations
U == 1 .. 9 \* array indices (process locations + 3 fixed processes)
u1 == 7 \* index for process 1
u2 == 8 \* index for process 2
u3 == 9 \* index for process 3
Loc == [min : V, halt : BOOLEAN]
AM == {W \in SUBSET(V \cup {unknown}) : W = {} \/ Cardinality(W) = 1 \/ (Cardinality(W) = 2 /\ unknown \in W)} \* abstract message alphabet  

\* translate index i \in I to location l \in Loc
location(i) ==
    LET x == i - 1 IN 
    LET m == IF x \div 2 = 0 THEN 0 ELSE IF x \div 2 = 1 THEN 1 ELSE 2 IN
    LET h == IF x % 2 = 0 THEN FALSE ELSE TRUE IN
    [min |-> m, halt |-> h]

\* translate location l \in Loc to index i \in I    
index(l) ==
    LET h == IF l.halt = FALSE THEN 0 ELSE 1 IN
    LET m == IF l.min = 0 THEN 0 ELSE IF l.min = 1 THEN 1 ELSE 2 IN
    2 * m + h + 1

\* get minimum value, given index u \in U  
min(u) ==
    IF u = u1
    THEN loc1.min
    ELSE IF u = u2
         THEN loc2.min
         ELSE IF u = u3 
              THEN loc3.min
              ELSE location(u).min    
    

\* Set of indices witnessing non-failed processes  
IndexNonFailed == {u1, u2, u3} \cup {index(l) : l \in {l1 \in locOther : ~l1.halt}}
\* Set of locations of active processes
Active == {loc1, loc2, loc3} \cup locOther 
\* Set of indices of correct processes (i.e., non-failed and non-crashed) 
Correct == {u1, u2, u3} \cup {index(l) : l \in {l1 \in locOther : ~l1.halt /\ crash[l1] # {TRUE}}}

\* set failure flag of l to TRUE  
failedLocation(l) ==
    [min |-> l.min, halt |-> TRUE]             
 
\* Set of initial locations    
InitActive == {[min |-> 0, halt |-> FALSE], 
               [min |-> 1, halt |-> FALSE],
               [min |-> 2, halt |-> FALSE]}

\* type invariant               
TypeOK ==
    /\ loc1 \in Loc
    /\ loc2 \in Loc
    /\ loc3 \in Loc
    /\ locOther \in SUBSET(Loc)
    /\ msgs \in [IndexNonFailed -> [IndexNonFailed -> AM]]
    /\ phase \in {"msgs", "trans"}
    /\ crash \in [{l \in locOther : ~l.halt} -> SUBSET(BOOLEAN)]
    /\ pclean \in BOOLEAN
    /\ decisionRound \in BOOLEAN    
    /\ receivers \in [{l \in DOMAIN crash : TRUE \in crash[l]} \X {u \in Correct : min(u) = 2} -> SUBSET(BOOLEAN)]
    /\ someP \in [{l \in locOther : ~l.halt /\ crash[l] # {TRUE} /\ l.min = 2} -> BOOLEAN]
               
\* initial predicate of the environment   
InitEnvironment == 
    /\ phase = "msgs"  \* current phase of the algorithm
    /\ decisionRound = FALSE  \* predicate for the decision round
    /\ crash \in [locOther -> ((SUBSET(BOOLEAN)) \ {{}})]  \* crash array 
    /\ pclean = FALSE \* predicate for the clean round
    /\ receivers \in [{l \in DOMAIN crash : TRUE \in crash[l]} \X {u \in Correct : min(u) = 2} -> ((SUBSET(BOOLEAN)) \ {{}})] \* receivers array 
    /\ someP = [l \in {k \in locOther : crash[k] # {TRUE} /\ k.min = 2} |-> FALSE]
    
\* initial predicate of the algorithm  
InitAlgorithm ==
    /\ loc1 \in InitActive \* first fixed process 
    /\ loc2 \in InitActive \* second fixed process 
    /\ loc3 \in InitActive \* third fixed process 
    /\ locOther \in ((SUBSET(InitActive)) \ {{}}) \* set of locations witnessing the other N - 2 processes
    /\ msgs = [u \in IndexNonFailed |-> [v \in IndexNonFailed |-> {unknown}]] \* two-dimensional messages array

\* environment transition in the message exchage phase 
MsgsEnvironment == 
    /\ phase' =  "trans" 
    /\ pclean' = IF \E l \in DOMAIN crash : (TRUE \in crash[l] /\ \A k \in DOMAIN crash : l # k => TRUE \notin crash[k])
                 THEN TRUE 
                 ELSE pclean 
    /\ decisionRound' \in IF pclean' THEN {TRUE, FALSE} ELSE {FALSE}
    /\ someP' \in [{l \in locOther : ~l.halt /\ crash[l] # {TRUE} /\ l.min = 2} -> BOOLEAN]
    /\ UNCHANGED <<crash, receivers>>
    
\* environment transition in the state update phase
TransEnvironment ==
    /\ phase' =  "msgs"
    /\ crash' \in [{l \in locOther' : ~l.halt} -> ((SUBSET(BOOLEAN)) \ {{}})]
    /\ receivers' \in [{l \in DOMAIN crash' : TRUE \in crash[l]'} \X {u \in TLCEval(Correct') : min(u)' = 2} -> ((SUBSET(BOOLEAN)) \ {{}})] \* /\ (l.W # loc1'.W \/ l.W # loc2'.W) \/ \E l1 \in locOther' : l.W # l1.W
    /\ someP' = [l \in {l \in locOther : ~l.halt /\ crash[l] # {TRUE} /\ l.min = 2}' |-> FALSE]  
    /\ UNCHANGED <<decisionRound, pclean>>

\* message generation function of a correct process
SendMessage(u, v) ==
    min(u)

\* update function of a correct process 
\* (that received the same messages as the abstract location that witnesses it)     
Update(l, u) == 
    LET m == IF l.min = 2 /\ \E v \in IndexNonFailed : 1 \in msgs[v][u]
             THEN IF \E v \in IndexNonFailed : 0 \in msgs[v][u]
                  THEN 0
                  ELSE 1
             ELSE IF l.min = 1 /\ \E v \in IndexNonFailed : 0 \in msgs[v][u]     
                  THEN 0
                  ELSE l.min IN
    LET h == IF decisionRound 
             THEN TRUE
             ELSE FALSE IN
    [min |-> m, halt |-> h]
    
\* update function of a correct process 
\* (that received messages different from the ones received by abstract location that witnesses it)
UpdateOther(l, m) ==
    LET h == IF decisionRound 
             THEN TRUE
             ELSE FALSE IN
    [min |-> m, halt |-> h]    

\* update of a process location witnessing correct processes    
UpdateCorrect(l, u) ==
    IF l.min = 2 /\ loc1.min = l.min /\ loc2.min = l.min /\ loc3.min = l.min
    THEN IF \A v \in IndexNonFailed : v \notin {u1, u2, u3} /\ min(v) # l.min => crash[location(v)] = {TRUE} /\ receivers[location(v), u] = {FALSE}
         THEN {UpdateOther(l, l.min)}
         ELSE IF someP[l]
              THEN {Update(l, u), UpdateOther(l, l.min)}
              ELSE {Update(l, u)} 
    ELSE {Update(l, u)}  
 
\* delivery of messages by the environment  
EnvSemMsg(m, u, v) ==
    IF u \in {u1, u2, u3}   
    THEN {m}
    ELSE LET l == location(u) IN
         IF crash[l] = {TRUE, FALSE}
         THEN IF min(v) = 2 /\ (v \in {u1, u2, u3} \/ crash[location(v)] # {TRUE})  
              THEN IF receivers[l,v] = {TRUE}
                   THEN {m}
                   ELSE {unknown, m}
              ELSE {unknown}                   
         ELSE IF crash[l] = {TRUE} 
              THEN IF min(v) = 2 /\ (v \in {u1, u2, u3} \/ crash[location(v)] # {TRUE})
                   THEN IF receivers[l,v] = {TRUE}
                        THEN {m}
                        ELSE IF receivers[l,v] = {FALSE}
                             THEN {unknown}
                             ELSE {unknown, m}
                   ELSE {unknown}          
              ELSE IF min(v) = 2 /\ (v \in {u1, u2, u3} \/ crash[location(v)] # {TRUE})
                   THEN {m}
                   ELSE {unknown} 

\* state update of the fixed processes w.r.t. the environment   
EnvSemState(l, u) ==
    IF l.halt
    THEN l
    ELSE TLCEval(Update(l, u))

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
    /\ UNCHANGED <<loc1, loc2, loc3, locOther>>

\* algorithm transition in the state update phase    
TransAlgorithm ==
    /\ loc1' = EnvSemState(loc1, u1)
    /\ loc2' = EnvSemState(loc2, u2)
    /\ loc3' = EnvSemState(loc2, u3)
    /\ locOther' = UNION{EnvSemStateOther(l) : l \in locOther} 
    /\ msgs' = [u \in IndexNonFailed' |-> [v \in IndexNonFailed' |-> {unknown}]]

NextEnvironment == 
    \/ phase = "msgs" /\ MsgsEnvironment
    \/ phase = "trans" /\ TransEnvironment

NextAlgorithm == 
    \/ phase = "msgs" /\ MsgsAlgorithm 
    \/ phase = "trans" /\ TransAlgorithm 

Init == InitAlgorithm /\ InitEnvironment    

Next == NextAlgorithm /\ NextEnvironment   

\* constraints
Fairness == /\ WF_vars(Next)
            /\ <>[](\E l \in DOMAIN crash : (TRUE \in crash[l] /\ \A k \in DOMAIN crash : l # k => TRUE \notin crash[k]))
            /\ <>decisionRound

\* specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* safety properties
\* k-Agreement: There is a subset W of V of cardinality K, such that all decision 
\*              values are in W  
Agreement == \E W \in SUBSET(V) : Cardinality(W) = K /\
             [](loc1.halt /\ loc2.halt /\ loc3.halt => 
                               (loc1.min \in W /\ loc2.min \in W /\ loc3.min \in W))
\* k-Validity: Any decision value for any process is the initial value of some process
Validity == \A W \in SUBSET(V) : W = {min(u) : u \in IndexNonFailed} =>
             [](loc1.halt /\ loc2.halt /\ loc3.halt => 
                               (loc1.min \in W /\ loc2.min \in W /\ loc3.min \in W))
\* liveness property                               
\* k-Termination: All correct processes eventually decide
Termination == <>(loc1.halt /\ loc2.halt /\ loc3.halt)

=============================================================================
