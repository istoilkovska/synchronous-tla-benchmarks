----------------------- MODULE fair_cons_abstract -----------------------

EXTENDS Naturals, FiniteSets, TLC

VARIABLES loc1, loc2, locOther, msgs, phase, crash, pclean, decisionRound, receivers, someP

vars == <<loc1, loc2, locOther, msgs, phase, crash, pclean, decisionRound, receivers, someP>>

unknown == 2
v0 == 0 \* default decision value
V == {0, 1} \* set of values
I == 1 .. 12 \* indices corresponding process locations
U == 1 .. 14 \* message array indices (process locations + 2 concrete processes)
u1 == 13 \* index for process 1
u2 == 14 \* index for process 2
Loc == [est : V, prev_est : V \cup {unknown}, halt : BOOLEAN] \* possible process locations
AM == {{0}, {1}, {unknown}, {0, unknown}, {1, unknown}} \* abstract message alphabets

\* translate index i \in I to location l \in Loc
location(i) ==
    LET x == i - 1 IN 
    LET p == IF x \div 4 = 0 THEN 0 ELSE IF x \div 4 = 1 THEN 1 ELSE unknown IN
    LET y == x % 4 IN
    LET e == IF y \div 2 = 0 THEN 0 ELSE 1 IN
    LET h == IF y % 2 = 0 THEN FALSE ELSE TRUE IN
    [est |-> e, prev_est |-> p, halt |-> h]

\* translate location l \in Loc to index i \in I  
index(l) ==
    LET h == IF l.halt = FALSE THEN 0 ELSE 1 IN
    LET e == IF l.est = 0 THEN 0 ELSE 1 IN
    LET p == IF l.prev_est = 0 THEN 0 ELSE IF l.prev_est = 1 THEN 1 ELSE 2 IN
    2 * e + 4 * p + h + 1

\* get value, given index u \in U      
estValue(u) ==
    IF u = u1
    THEN loc1.est
    ELSE IF u = u2
         THEN loc2.est
         ELSE location(u).est 

\* get previous value, given index u \in U           
prevEstValue(u) ==
    IF u = u1
    THEN loc1.prev_est
    ELSE IF u = u2
         THEN loc2.prev_est
         ELSE location(u).prev_est          

\* Set of indices witnessing non-failed processes    
IndexNonFailed == {u1, u2} \cup {index(l) : l \in {l1 \in locOther : ~l1.halt}}
\* Set of locations of active processes
Active == {loc1, loc2} \cup locOther 
\* Set of indices of correct processes (i.e., non-failed and non-crashed) 
Correct == {u1, u2} \cup {index(l) : l \in {l1 \in locOther : ~l1.halt /\ crash[l1] # {TRUE}}}

\* set failure flag of l to TRUE
failedLocation(l) ==
    [est |-> l.est, prev_est |-> l.prev_est, halt |-> TRUE]

\* Set of initial locations    
InitActive == {[est |-> 0, prev_est |-> unknown, halt |-> FALSE], 
               [est |-> 1, prev_est |-> unknown, halt |-> FALSE]}   

\* type invariant
TypeOK ==
    /\ loc1 \in Loc
    /\ loc2 \in Loc
    /\ locOther \in SUBSET(Loc)
    /\ msgs \in [IndexNonFailed -> [IndexNonFailed -> AM]]
    /\ phase \in {"msgs", "trans"}
    /\ crash \in [{l \in locOther : ~l.halt} -> SUBSET(BOOLEAN)]
    /\ pclean \in BOOLEAN
    /\ decisionRound \in BOOLEAN    
    /\ receivers \in [{l \in DOMAIN crash : TRUE \in crash[l]} \X {u \in Correct : estValue(u) = 1} -> SUBSET(BOOLEAN)]
    /\ someP \in [{l \in locOther : ~l.halt /\ l.est = 1} -> BOOLEAN]
 
\* initial predicate of the environment    
InitEnvironment == 
    /\ phase = "msgs" \* current phase of the algorithm
    /\ decisionRound = FALSE \* termination round predicate
    /\ crash \in [locOther -> ((SUBSET(BOOLEAN)) \ {{}})] \* crash array
    /\ pclean = FALSE \* clean round predicate
    /\ receivers \in [{l \in DOMAIN crash : TRUE \in crash[l]} \X Correct -> ((SUBSET(BOOLEAN)) \ {{}})] \* receivers array
    /\ someP = [l \in locOther |-> FALSE]

\* initial predicate of the algorithm      
InitAlgorithm ==
    /\ loc1 \in InitActive \* first process kept explicitly
    /\ loc2 \in InitActive \* second process kept explicitly
    /\ locOther \in ((SUBSET(InitActive)) \ {{}}) \* set of witnesses for the other N - 2 processes
    /\ msgs = [u \in IndexNonFailed |-> [v \in IndexNonFailed |-> {unknown}]]  \* two-dimensional messages array

\* environment transition in the message exchage phase     
MsgsEnvironment ==
    /\ phase' =  "trans"
    /\ pclean' = IF \A l \in DOMAIN crash : TRUE \notin crash[l] THEN TRUE ELSE pclean
    /\ decisionRound' \in IF pclean' THEN {TRUE, FALSE} ELSE {FALSE}
    /\ someP' \in [{l \in locOther : ~l.halt /\ l.est = 1} -> BOOLEAN]
    /\ UNCHANGED <<crash, receivers>>

\* environment transition in the state update phase  
TransEnvironment ==
    /\ phase' =  "msgs"
    /\ crash' \in [{l \in locOther' : ~l.halt} -> ((SUBSET(BOOLEAN)) \ {{}})]
    /\ receivers' \in [{l \in DOMAIN crash' : TRUE \in crash[l]'} 
                        \X {u \in Correct' : estValue(u)' = 1} 
                                                                        -> (SUBSET(BOOLEAN) \ {{}})]
    /\ someP' = [l \in {l \in locOther : ~l.halt /\ l.est = 1 /\ crash[l] # {TRUE}}' |-> FALSE]                                                                        
    /\ UNCHANGED <<decisionRound, pclean>>
    
\* message generation function of a correct process
SendMessage(u, v) ==
    IF estValue(u) # prevEstValue(u)
    THEN estValue(u)
    ELSE unknown      

\* update function of a correct process 
\* (that received the same messages as the abstract location that witnesses it) 
Update(l, u) ==
    LET e == IF l.est = 1 /\ \E v \in IndexNonFailed : 0 \in msgs[v][u]
             THEN 0
             ELSE l.est IN
    LET h == IF decisionRound 
             THEN TRUE
             ELSE FALSE IN
    [est |-> e, prev_est |-> l.est, halt |-> h]  

\* update function of a correct process 
\* (that received messages different from the ones received by abstract location that witnesses it)
UpdateOther(l, e) ==
    LET h == IF decisionRound 
             THEN TRUE
             ELSE FALSE IN
    [est |-> e, prev_est |-> l.est, halt |-> h]  

\* update of a process location witnessing correct processes
UpdateCorrect(l, u) == 
    IF l.est = 1 /\ loc1.est = l.est /\ loc2.est = l.est
    THEN IF \A v \in IndexNonFailed : v \notin {u1, u2} /\ location(v).est # l.est => crash[location(v)] = {TRUE} /\ receivers[location(v), u] = {FALSE}
         THEN {UpdateOther(l, l.est)}
         ELSE IF someP[l]
              THEN {Update(l, u), UpdateOther(l, l.est)}
              ELSE {Update(l, u)}
    ELSE {Update(l, u)}
 
\* delivery of messages by the environment   
EnvSemMsg(m, u, v) ==
    IF u \in {u1, u2}   
    THEN {m}
    ELSE LET l == location(u) IN
         IF crash[l] = {TRUE, FALSE}
         THEN IF estValue(v) = 1 /\ (v \in {u1, u2} \/ crash[location(v)] # {TRUE})  
              THEN IF receivers[l,v] = {TRUE}
                   THEN {m}
                   ELSE {unknown, m}
              ELSE {unknown}                   
         ELSE IF crash[l] = {TRUE} 
              THEN IF estValue(v) = 1 /\ (v \in {u1, u2} \/ crash[location(v)] # {TRUE})
                   THEN IF receivers[l,v] = {TRUE}
                        THEN {m}
                        ELSE IF receivers[l,v] = {FALSE}
                             THEN {unknown}
                             ELSE {unknown, m}
                   ELSE {unknown}          
              ELSE IF estValue(v) = 1 /\ (v \in {u1, u2} \/ crash[location(v)] # {TRUE})
                   THEN {m}
                   ELSE {unknown}

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
         ELSE IF crash[l] = {TRUE, FALSE}  \* some processes witnessed by l crashed, and some not
              THEN  UpdateCorrect(l, index(l)) \cup {failedLocation(l)} 
              ELSE  UpdateCorrect(l, index(l)) \* no processes witnessed by l crashed

\* algorithm transition in the message exchange phase
MsgsAlgorithm == 
    /\ msgs' = [u \in IndexNonFailed |-> [v \in IndexNonFailed |-> EnvSemMsg(SendMessage(u, v), u, v)]]
    /\ UNCHANGED <<loc1, loc2, locOther>> 

\* algorithm transition in the state update phase
TransAlgorithm ==
    /\ loc1' = EnvSemState(loc1, u1)
    /\ loc2' = EnvSemState(loc2, u2)
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
Fairness == 
    /\ WF_vars(Next)
    /\ <>[](\A l \in DOMAIN crash : TRUE \notin crash[l])
    /\ <>decisionRound

\* specification    
Spec == Init /\ [][Next]_vars /\ Fairness

\* safety properties
Validity0 == ((\A l \in Active : l.est = 0) => 
                            [](/\ loc1.halt => loc1.est = 0
                               /\ loc2.halt => loc2.est = 0))
Validity1 == ((\A l \in Active : l.est = 1) => 
                            [](/\ loc1.halt => loc1.est = 1
                               /\ loc2.halt => loc2.est = 1))
\* Validity: if all processes start with the same value, then this is the only 
\*           possible decision value
Validity == Validity0 /\ Validity1

\* Agreement: no two correct processes decide on a different value
Agreement == [](loc1.halt /\ loc2.halt => loc1.est = loc2.est)

\* liveness property
\* Termination: all correct processes eventually decide
Termination == <>(loc1.halt /\ loc2.halt)

=============================================================================
\* Modification History
\* Last modified Tue Oct 17 15:07:25 CEST 2017 by stoilkov
\* Created Mon Sep 25 15:12:35 CEST 2017 by stoilkov
