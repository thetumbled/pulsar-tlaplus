------------------------- MODULE compaction -------------------------
EXTENDS Naturals, FiniteSets, Sequences, Integers, TLC

(*
This specification model the topic compaction feature of pulsar.
There are three roles in the system: producer, consumer and compactor.
For simplicity, we use index to represent the MessageId, index from 1 to MessageSentLimit.
*)

\* Input parameters
CONSTANTS MessageSentLimit, \* The maximum number of messages that can be sent
          CompactionTimesLimit, \* The maximum number of compaction times
          ModelConsumer, \* whether model consumer is enabled
          ConsumeTimesLimit, \* The maximum number of consume times
          KeySpace, \* The key space for producer to generate keys
          ValueSpace, \* The value space for producer to generate values
          RetainNullKey, \* whether retains null key message in compacted ledger
          MaxCrashTimes \* The maximum number of crash times

ASSUME /\ MessageSentLimit \in Nat
       /\ CompactionTimesLimit \in Nat
       /\ ModelConsumer \in BOOLEAN
       /\ ConsumeTimesLimit \in Nat
       /\ KeySpace \in SUBSET Nat
       /\ ValueSpace \in SUBSET Nat
       /\ RetainNullKey \in BOOLEAN
       /\ MaxCrashTimes \in Nat

\* Model values
CONSTANTS Nil, \* The nil value
          Compactor_In_PhaseOne, \* The compactor is in phase one
          Compactor_In_PhaseTwoWrite, \* The compactor is in phase two write
          Compactor_In_PhaseTwoUpdateContext, \* The compactor is in phase two update context
          Compactor_In_PhaseTwoUpdateHorizon, \* The compactor is in phase two update horizon
          Compactor_In_PhaseTwoPersistCusror, \* The compactor is in phase two persist cursor
          Compactor_In_PhaseTwoDeleteLedger \* The compactor is in phase two delete ledger


NullKey == 0 \* The nil key
NullValue == 0 \* The nil value
KeySet == KeySpace \cup {NullKey} \* The key set, 0 is reserved for the nil key
ValueSet == ValueSpace \cup {NullValue} \* The value set, 0 is reserved for the nil value

CompactorState == {Compactor_In_PhaseOne, Compactor_In_PhaseTwoWrite, Compactor_In_PhaseTwoUpdateContext,
                   Compactor_In_PhaseTwoUpdateHorizon, Compactor_In_PhaseTwoPersistCusror,
                   Compactor_In_PhaseTwoDeleteLedger}

\* bookkeeping the messages
VARIABLES messages, \* bookkeeping the messages, queue of messages
          compactedLedgers,  \* bookkeeping the compacted messages,
                             \* mapping from the compacted ledger id to the original message queue
          cursor \* the cursor of __compaction, record the current compaction position and the compacted ledger

\* variables for the compactor
VARIABLES compactorState,    \* the state of the compactor
          phaseOneResult,     \* the result of phase one compaction, model Map<String, MessageId> latestForKey
          compactionHorizon,  \* the compaction horizon, model the compaction position
          compactedTopicContext \* the compacted topic context, model the compacted ledger

\* some other variables
VARIABLES crashTimes \* the crash times of the broker

bookieVars == <<messages, compactedLedgers>>
compactorVars == <<phaseOneResult, compactorState, compactionHorizon, compactedTopicContext>>
otherVars == <<crashTimes>>
vars == <<bookieVars, compactorVars, otherVars>>


\* producer sends messages
\* may be we could replace the producer with pre-defined messages to minimize the state space
ConstructMessage(inputKey, inputValue) ==
    [key |-> inputKey, value |-> inputValue]

Producer ==
    /\ Len(messages) < MessageSentLimit
    /\ \E inputKey \in KeySet, inputValue \in ValueSet:
        messages' = Append(messages, ConstructMessage(inputKey, inputValue))
    /\ UNCHANGED <<compactedLedgers, cursor, compactorVars, otherVars>>


\* compactor compacts messages
Max(s) == CHOOSE x \in s: \A y \in s: x >= y
GetKeys(msgs) == {msgs[i].key : i \in 1..Len(msgs)} \ {NullKey}
CompactorPhaseOne ==
    /\ compactorState = Compactor_In_PhaseOne
    /\ phaseOneResult = Nil
    /\ phaseOneResult' = [key \in GetKeys(messages) |-> Max({i \in 1..Len(messages) : messages[i].key = key})]
    /\ compactorState' = Compactor_In_PhaseTwoWrite
    /\ UNCHANGED <<bookieVars, otherVars, compactionHorizon, compactedTopicContext>>

\* create a new compacted ledger and compact the messages
MaxCompactedLedgerId(compactedLedgers2) == Max({i \in 1..CompactionTimesLimit : compactedLedgers2[i] # Nil})
CompactMessages(messages2, phaseOneResult2) ==
    LET
        compactedMessages == [i \in 1..Len(messages2) |->
                                IF messages2[i].key = NullKey
                                THEN IF RetainNullKey
                                     THEN messages2[i]
                                     ELSE Nil
                                ELSE IF i = phaseOneResult2[messages2[i].key]
                                     THEN messages2[i]
                                     ELSE Nil]
        ValidIndex == {i \in 1..Len(compactedMessages) : compactedMessages[i] # Nil}
    IN
        \* filter out the nil messages
        [i \in ValidIndex |-> compactedMessages[i]]

CompactorPhaseTwoWrite ==
    /\ phaseOneResult # Nil
    /\ compactorState = Compactor_In_PhaseTwoWrite
    /\ LET
        maxledgerId == MaxCompactedLedgerId(compactedLedgers)
        newCompactedLedgerId == maxledgerId + 1
        compactedMessages == CompactMessages(messages, phaseOneResult)
       IN
        /\ newCompactedLedgerId \in 1..CompactionTimesLimit
        /\ compactedLedgers' = [compactedLedgers EXCEPT ![newCompactedLedgerId] = compactedMessages]
    /\ phaseOneResult' = Nil
    /\ compactorState' = Compactor_In_PhaseTwoUpdateContext
    /\ UNCHANGED <<messages, cursor, otherVars, compactionHorizon, compactedTopicContext>>


CompactorPhaseTwoUpdateContext ==
    /\ compactorState = Compactor_In_PhaseTwoUpdateContext
    /\ compactorState' = Compactor_In_PhaseTwoUpdateHorizon
    /\ compactedTopicContext' = MaxCompactedLedgerId(compactedLedgers)
    /\ UNCHANGED <<bookieVars, otherVars, compactorVars, phaseOneResult, compactionHorizon>>

CompactorPhaseTwoUpdateHorizon ==
    /\ compactorState = Compactor_In_PhaseTwoUpdateHorizon
    /\ compactorState' = Compactor_In_PhaseTwoPersistCusror
    /\ compactionHorizon' = MaxCompactedLedgerId(compactedLedgers)
    /\ UNCHANGED <<bookieVars, otherVars, compactorVars, phaseOneResult, compactedTopicContext>>

CompactorPhaseTwoPersistCusror ==
    /\ compactorState = Compactor_In_PhaseTwoPersistCusror
    /\ compactorState' = Compactor_In_PhaseTwoDeleteLedger
    /\ cursor' = [compactionHorizon: compactionHorizon, compactedTopicContext: compactedTopicContext]
    /\ UNCHANGED <<messages, compactedLedgers, otherVars, phaseOneResult, compactionHorizon, compactedTopicContext>>

CompactorPhaseTwoDeleteLedger ==
    /\ compactorState = Compactor_In_PhaseTwoDeleteLedger
    /\ compactorState' = Compactor_In_PhaseOne
    /\ LET
        maxledgerId == MaxCompactedLedgerId(compactedLedgers)
        \* for simplicity, we delete the second to last compacted ledger
        oldCompactedLedgerId == IF maxledgerId = 1 THEN Nil ELSE maxledgerId - 1
       IN
         IF compactedLedgers[oldCompactedLedgerId] = Nil
         THEN compactedLedgers' = compactedLedgers
         ELSE compactedLedgers' = [compactedLedgers EXCEPT ![oldCompactedLedgerId] = Nil]
    /\ UNCHANGED <<messages, cursor, otherVars, compactorVars, phaseOneResult, compactedTopicContext, compactionHorizon>>


\* broker crashes, that is compactor crashes
BrokerCrash ==
    /\ crashTimes < MaxCrashTimes
    /\ crashTimes' = crashTimes + 1
    \* reset compactor state and phase one result
    /\ compactorState' = Compactor_In_PhaseOne
    /\ phaseOneResult' = Nil
    \* reload the compaction horizon and compacted topic context from cursor
    /\ compactionHorizon' = cursor.compactionHorizon
    /\ compactedTopicContext' = cursor.compactedTopicContext
    /\ UNCHANGED <<bookieVars, otherVars>>

\* Consumer consumes messages
Consumer ==
    UNCHANGED vars

Init ==
    /\ messages = <<>>
    /\ compactedLedgers = [i \in 1..CompactionTimesLimit |-> Nil]
    /\ phaseOneResult = Nil
    /\ compactorState = Compactor_In_PhaseOne
    /\ compactionHorizon = Nil
    /\ compactedTopicContext = Nil
    /\ crashTimes = 0
    /\ cursor = Nil

Next ==
    \* The producer
    \/ Producer
    \* The compactor
    \/ CompactorPhaseOne
    \/ CompactorPhaseTwoWrite
    \/ CompactorPhaseTwoUpdateContext
    \/ CompactorPhaseTwoUpdateHorizon
    \/ CompactorPhaseTwoPersistCusror
    \/ CompactorPhaseTwoDeleteLedger
    \/ BrokerCrash
    \* The consumer
    \/ /\ ModelConsumer
       /\ Consumer

Spec == Init /\ [][Next]_vars

\* Safety properties
TypeSafe ==
    /\ messages \in Seq([key: KeySet, value: ValueSet])
    /\ compactedLedgers \in [1..CompactionTimesLimit -> Seq([key: KeySet, value: ValueSet])]
    /\ phaseOneResult \in [KeySet -> 1..MessageSentLimit]
    /\ compactorState \in CompactorState
    /\ compactionHorizon \in 1..MessageSentLimit
    /\ compactedTopicContext \in 1..CompactionTimesLimit
    /\ crashTimes \in 0..(MaxCrashTimes-1)
    /\ cursor \in [compactionHorizon: 1..MessageSentLimit, compactedTopicContext: 1..CompactionTimesLimit]


\* the useless compacted ledger should be deleted, we model deletion as Nil
CompactedLedgerLeak == Cardinality({i \in 1..CompactionTimesLimit : compactedLedgers[i] # Nil}) <= 2

\* consumer should be able to consume all the compacted messages


\* Liveness properties

=============================================================================