----------------------- MODULE edac_abstract_m1 -----------------------

EXTENDS Naturals, FiniteSets, TLC

VARIABLES loc1, locOther, msgs, previous, phase, crash, decisionRound, receivers, someP

vars == <<loc1, locOther, msgs, previous, phase, crash, decisionRound, receivers, someP>>

v0 == 0 \* default decision value
V == {0, 1} \* set of values
I == 1 .. 12 \* indices corresponding process locations
U == 1 .. 13 \* array indices (process locations + 1 fixed process)
u1 == 13 \* index for process 1
Loc == [ W : {{0}, {1}, {0, 1}}, halt : BOOLEAN, decide : BOOLEAN] \* possible process locations
AM == {W \in SUBSET(SUBSET(V)) : W = {} \/ Cardinality(W) = 1 \/ (Cardinality(W) = 2 /\ {} \in W)} \* abstract message alphabet

\* translate index i \in I to location l \in Loc
location(i) ==
    LET x == i - 1 IN 
    LET w == IF x \div 4 = 0 THEN {0} ELSE IF x \div 4 = 1 THEN {1} ELSE {0, 1} IN
    LET y == x % 4 IN
    LET h == IF y \div 2 = 0 THEN FALSE ELSE TRUE IN
    LET d == IF y % 2 = 0 THEN FALSE ELSE TRUE IN
    [W |-> w, halt |-> h, decide |-> d]
  
\* translate location l \in Loc to index i \in I    
index(l) ==
    LET d == IF l.decide = FALSE THEN 0 ELSE 1 IN
    LET h == IF l.halt = FALSE THEN 0 ELSE 1 IN
    LET w == IF l.W = {0} THEN 0 ELSE IF l.W = {1} THEN 1 ELSE 2 IN
    4 * w + 2 * h + d + 1

\* get value set, given index u \in U       
valueSet(u) ==
    IF u = u1
    THEN loc1.W
    ELSE location(u).W   
\* get decided flag, given index u \in U            
decided(u) ==
    IF u = u1
    THEN loc1.decide
    ELSE location(u).decide       
\* get halted flag, given index u \in U              
halted(u) ==
    IF u = u1
    THEN loc1.halt
    ELSE location(u).halt  
    
\* Set of locations of active processes
Active == {loc1} \cup locOther 
\* Set of indices of active processes
IndexActive == {u1} \cup {index(l) : l \in locOther}  
\* Set of indices witnessing non-halted processes  
IndexNonHalted == {u \in IndexActive : ~halted(u)}
\* Set of indices witnessing undecided processes  
IndexUndecided == {u \in IndexActive : ~halted(u) /\ ~decided(u)} 
\* Set of indices of correct processes (i.e., non-failed and non-crashed) 
Correct == {u \in IndexActive : ~halted(u) /\ ~decided(u) /\ (u \in {u1} \/ crash[location(u)] # {TRUE})}

\* set failure flag of l to TRUE  
failedLocation(l) ==
    [W |-> l.W, halt |-> TRUE, decide |-> l.decide]

\* a process in a decided location stops participating in the algorithm  
decidedLocation(l) ==
    [W |-> l.W, halt |-> TRUE, decide |-> TRUE]   

\* Set of initial locations       
InitActive == {[W |-> {0}, halt |-> FALSE, decide |-> FALSE], 
               [W |-> {1}, halt |-> FALSE, decide |-> FALSE]}   

\* type invariant
TypeOK ==
    /\ loc1 \in Loc
    /\ locOther \in SUBSET(Loc)
    /\ msgs \in [IndexNonHalted -> [IndexNonHalted -> AM]]
    /\ phase \in {"msgs", "trans"}
    /\ crash \in [{l \in locOther : ~l.halt} -> SUBSET(BOOLEAN)]
    /\ decisionRound \in [Correct -> BOOLEAN]
    /\ receivers \in [{l \in DOMAIN crash : TRUE \in crash[l]} \X {u \in Correct : Cardinality(valueSet(u)) = 1} -> SUBSET(BOOLEAN)]
    /\ someP \in [{l \in locOther : ~l.halt /\ Cardinality(l.W) = 1 /\ crash[l] # {TRUE}} -> BOOLEAN]

\* initial predicate of the environment    
InitEnvironment == 
    /\ phase = "msgs" \* current phase of the algorithm
    /\ crash \in [locOther -> ((SUBSET(BOOLEAN)) \ {{}})] \* crash array 
    /\ decisionRound = [u \in Correct |-> FALSE] \* early decision predicates for the correct processes
    /\ receivers \in [{l \in DOMAIN crash : TRUE \in crash[l]} \X Correct -> ((SUBSET(BOOLEAN)) \ {{}})]  \* receivers array
    /\ someP = [l \in {k \in locOther : crash[k] # {TRUE}} |-> FALSE]
    
InitAlgorithm ==
    /\ loc1 \in InitActive \* first fixed process
    /\ locOther \in ((SUBSET(InitActive)) \ {{}})  \* set of locations witnessing the other N - 2 processes
    /\ msgs = [u \in IndexNonHalted |-> [v \in IndexNonHalted |-> {<<>>}]]  \* two-dimensional messages array
    /\ previous = [u \in IndexNonHalted |-> [v \in IndexUndecided |-> {}]] \* {} ]]  \* two-dimensional array storing messages from the previous round
 
\* equality of messages between the previous and current round    
equal(u, v) ==
    IF <<>> \in msgs[u][v]'
    THEN previous[u][v] = msgs[u][v]' 
    ELSE previous[u][v] # {<<>>} /\ msgs[u][v]' \subseteq previous[u][v] 
   
\* check for equality of messages received in the previous and the current round     
\* by processes witnessed by v
isDecisionRound(v) ==
    \A u \in IndexNonHalted : equal(u, v)

\* environment transition in the message exchage phase  
MsgsEnvironment ==
    /\ phase' = "trans"
    /\ decisionRound' = [v \in Correct |-> isDecisionRound(v)]
    /\ someP' \in [{l \in locOther : ~l.halt /\ Cardinality(l.W) = 1 /\ crash[l] # {TRUE}} -> BOOLEAN]
    /\ UNCHANGED <<crash, receivers>>

\* environment transition in the state update phase
TransEnvironment ==
    /\ phase' =  "msgs"
    /\ crash' \in [{l \in locOther' : ~l.halt} -> ((SUBSET(BOOLEAN)) \ {{}})]
    /\ receivers' \in [{l \in DOMAIN crash' : TRUE \in crash[l]'} 
                        \times {u \in Correct' : Cardinality(valueSet(u)') = 1} 
                                                                        -> (SUBSET(BOOLEAN) \ {{}})]
    /\ someP' = [l \in {k \in locOther : ~k.halt /\ Cardinality(k.W) = 1 /\ crash[k] # {TRUE}}' |-> FALSE]
    /\ UNCHANGED <<decisionRound>>

\* message generation function of a correct process
SendMessage(u, v) ==
    <<valueSet(u), decided(u)>>      

\* update function of a correct process 
\* (that received the same messages as the abstract location that witnesses it) 
Update(l, u) ==
    LET arrived == {m \in V : \E v \in IndexNonHalted : <<{m}, TRUE>> \in msgs[v][u]} IN 
    LET x == IF \/ /\ l.W = {0} 
                   /\ \E m \in {{1}, {0, 1}} : \E v \in IndexNonHalted : <<m, FALSE>> \in msgs[v][u]  
                \/ /\ l.W = {1}
                   /\ \E m \in {{0}, {0, 1}} : \E v \in IndexNonHalted : <<m, FALSE>> \in msgs[v][u]
             THEN {0, 1}
             ELSE l.W IN
    LET w == IF arrived # {}
             THEN arrived
             ELSE IF decisionRound[u]
                  THEN IF x = {0}
                       THEN {0}
                       ELSE IF x = {1}
                            THEN {1}
                            ELSE {v0}
                  ELSE x IN
    LET h == IF l.decide 
             THEN TRUE
             ELSE FALSE IN
    LET d == IF arrived # {} \/ decisionRound[u]
             THEN TRUE 
             ELSE FALSE IN             
    [W |-> w, halt |-> h, decide |-> d]  

\* update function of a correct process 
\* (that received messages different from the ones received by abstract location that witnesses it)
UpdateOther(l, u, M) ==
    LET arrived == {m \in V : \E v \in IndexNonHalted : <<{m}, TRUE>> \in msgs[v][u]} IN
    LET w == IF arrived # {}
             THEN arrived
             ELSE IF decisionRound[u]
                  THEN IF l.W \cup M = {0}
                       THEN {0}
                       ELSE IF l.W \cup M = {1}
                            THEN {1}
                            ELSE {v0}
                       ELSE l.W \cup M IN
    LET h == IF l.decide 
             THEN TRUE
             ELSE FALSE IN
    LET d == IF arrived # {} \/ decisionRound[u]
             THEN TRUE 
             ELSE FALSE IN
    [W |-> w, halt |-> h, decide |-> d]              

\* update of a process location witnessing correct processes
UpdateCorrect(l, u) == 
    IF \A m \in V : \A v \in IndexNonHalted : <<{m}, TRUE>> \notin msgs[v][u]
    THEN IF Cardinality(l.W) = 1 /\ loc1.W = l.W
         THEN IF \A v \in IndexNonHalted : v \notin {u1} /\ location(v).W # l.W => crash[location(v)] = {TRUE} /\ receivers[location(v), u] = {FALSE}
              THEN {UpdateOther(l, u, l.W)}
              ELSE IF someP[l]
                   THEN {Update(l, u), UpdateOther(l, u, l.W)}
                   ELSE {Update(l, u)}
         ELSE {Update(l, u)}  
    ELSE {Update(l, u)}         

\* delivery of messages by the environment 
EnvSemMsg(m, u, v) ==
    IF u \in {u1}   
    THEN {m}
    ELSE LET l == location(u) IN
         IF crash[l] = {TRUE, FALSE}
         THEN IF ~decided(v) /\ Cardinality(valueSet(v)) = 1 /\ (v \in {u1} \/ crash[location(v)] # {TRUE})  
              THEN IF receivers[l,v] = {TRUE}
                   THEN {m}
                   ELSE {<<>>, m}
              ELSE {<<>>}                   
         ELSE IF crash[l] = {TRUE} 
              THEN IF ~decided(v) /\ Cardinality(valueSet(v)) = 1 /\ (v \in {u1} \/ crash[location(v)] # {TRUE})
                   THEN IF receivers[l,v] = {TRUE}
                        THEN {m}
                        ELSE IF receivers[l,v] = {FALSE}
                             THEN {<<>>}
                             ELSE {<<>>, m}
                   ELSE {<<>>}          
              ELSE IF ~decided(v) /\ Cardinality(valueSet(v)) = 1 /\ (v \in {u1} \/ crash[location(v)] # {TRUE})
                   THEN {m}
                   ELSE {<<>>}

\* state update of the fixed processes w.r.t. the environment 
EnvSemState(l, u) ==
    IF l.halt
    THEN l
    ELSE IF l.decide
         THEN decidedLocation(l)
         ELSE Update(l, u)

\* state update of the other processes w.r.t. the environment
EnvSemStateOther(l) ==
    IF l.halt
    THEN {l} \* halted processes do not update their location
    ELSE IF l.decide \* if processes have decided, there is no need in processing received messages
         THEN {decidedLocation(l)} \* processes that decided in the previous round halt in this round
         ELSE IF crash[l] = {TRUE} \* all processes in l have crashed in this round
              THEN {failedLocation(l)} \* they are flagged as failed in the next rounds 
              ELSE IF crash[l] = {TRUE, FALSE} \* some processes in l crashed, and some did not
                   THEN UpdateCorrect(l, index(l)) \cup {failedLocation(l)} \* partially correct, partially failed
                   ELSE UpdateCorrect(l, index(l)) \* no failed (fully correct)

\* update of messages               
UpdatePrevious(u, v) ==
    LET E == IF u \in {u1} 
             THEN {u}
             ELSE {index(k) : k \in {l \in locOther : location(u) \in EnvSemStateOther(l)}} IN
    LET F == IF v \in {u1}
             THEN {v}
             ELSE {index(k) : k \in {l \in locOther : location(v) \in EnvSemStateOther(l)}} IN
UNION({msgs[e][f] : e \in E, f \in F})

\* algorithm transition in the message exchange phase
MsgsAlgorithm == 
    /\ msgs' = [u \in IndexNonHalted |-> [v \in IndexNonHalted |-> EnvSemMsg(SendMessage(u, v), u, v)]]
    /\ UNCHANGED <<loc1, locOther, previous>> 

\* local state transition phase of the algorithm module    
TransAlgorithm ==
    /\ loc1' = EnvSemState(loc1, u1)
    /\ locOther' = UNION{EnvSemStateOther(l) : l \in locOther}  
    /\ previous' = [u \in IndexNonHalted' |-> [v \in IndexUndecided' |-> UpdatePrevious(u, v)]]
    /\ msgs' = [u \in IndexNonHalted' |-> [v \in IndexNonHalted' |-> {<<>>}]]
    
    
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
    /\ <>[](\A c \in DOMAIN crash : TRUE \notin crash[c])

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
\* Last modified Tue Oct 17 11:50:19 CEST 2017 by stoilkov
\* Created Thu Sep 28 17:11:33 CEST 2017 by stoilkov
