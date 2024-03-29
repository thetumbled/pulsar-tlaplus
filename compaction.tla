------------------------- MODULE compaction -------------------------
EXTENDS Naturals, FiniteSets, Sequences, Integers, TLC

(*
This specification model the topic compaction feature of pulsar.
There are three roles in the system: producer, consumer and compactor.
*)

\* Input parameters
CONSTANTS MessageSentLimit, \* The maximum number of messages that can be sent
          CompactionTimesLimit, \* The maximum number of compaction times
          ModelConsumer, \* whether model consumer is enabled
          ConsumeTimesLimit, \* The maximum number of consume times
          KeySpace, \* The key space for producer to generate keys
          ValueSpace, \* The value space for producer to generate values
          RetainNullKey, \* whether retains null key message in compacted ledger
          MaxCrashTimes, \* The maximum number of crash times
          ModelProducer \* whether model producer is enabled
                               \* if it is set to false, we will pregenerate messages to replace the producer
                               \* which can reduce the state space significantly.
                               \* as there is few chance to find a bug involving the producer,
                               \* we can set it to false to speed up the model checking
                               \* if disable modelling of consumer and producer, the state space decrease from 253361 to 45198

ASSUME /\ MessageSentLimit \in Nat
       /\ CompactionTimesLimit \in Nat
       /\ ModelConsumer \in BOOLEAN
       /\ ConsumeTimesLimit \in Nat
       /\ KeySpace \in SUBSET Nat
       /\ 0 \notin KeySpace \* 0 is reserved for the nil key
       /\ ValueSpace \in SUBSET Nat
       /\ 0 \notin ValueSpace \* 0 is reserved for the null message
       /\ RetainNullKey \in BOOLEAN
       /\ MaxCrashTimes \in Nat
       /\ ModelProducer \in BOOLEAN

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
          phaseOneResult,     \* the result of phase one compaction, model Map<String, MessageId> latestForKey and int readPosition
          compactionHorizon,  \* the compaction horizon, model the compaction position
          compactedTopicContext \* the compacted topic context, model the compacted ledger

\* some other variables
VARIABLES crashTimes, \* the crash times of the broker
          consumeTimes \* the consume times of the consumer

bookieVars == <<messages, compactedLedgers, cursor>>
compactorVars == <<phaseOneResult, compactorState, compactionHorizon, compactedTopicContext>>
otherVars == <<crashTimes, consumeTimes>>
vars == <<bookieVars, compactorVars, otherVars>>


\* producer sends messages
\* may be we could replace the producer with pre-defined messages to minimize the state space
ConstructMessage(inputId, inputKey, inputValue) ==
    [id |-> inputId, key |-> inputKey, value |-> inputValue]

Producer ==
    /\ Len(messages) < MessageSentLimit
    /\ \E inputKey \in KeySet, inputValue \in ValueSet:
        messages' = Append(messages, ConstructMessage(Len(messages) + 1, inputKey, inputValue))
    /\ UNCHANGED <<compactedLedgers, cursor, compactorVars, otherVars>>


\* compactor compacts messages
Max(s) == CHOOSE x \in s: \A y \in s: x >= y
GetKeys(msgs) == {msgs[i].key : i \in 1..Len(msgs)} \ {NullKey}
CompactorPhaseOne ==
    /\ compactorState = Compactor_In_PhaseOne
    /\ phaseOneResult = Nil
    /\ Len(messages) > 0 \* there are messages to be compacted
    /\ phaseOneResult' = [readPosition |-> Len(messages),
            latestForKey |-> [key \in GetKeys(messages) |-> Max({i \in 1..Len(messages) : messages[i].key = key})]]
    /\ compactorState' = Compactor_In_PhaseTwoWrite
    /\ UNCHANGED <<bookieVars, otherVars, compactionHorizon, compactedTopicContext>>

\* create a new compacted ledger and compact the messages
MaxCompactedLedgerId(compactedLedgers2) ==
    IF \E i \in 1..CompactionTimesLimit: compactedLedgers2[i] # Nil
    THEN Max({i \in 1..CompactionTimesLimit : compactedLedgers2[i] # Nil})
    ELSE 0
CompactMessages(messages2, phaseOneResult2) ==
    LET
        compactedMessages == [i \in 1..phaseOneResult2.readPosition |->
                                IF messages2[i].key = NullKey
                                THEN IF RetainNullKey
                                     THEN messages2[i]
                                     ELSE Nil
                                ELSE IF i = phaseOneResult2.latestForKey[messages2[i].key]
                                     THEN messages2[i]
                                     ELSE Nil]
    IN
        \* filter out the nil messages by SelectSeq.
        SelectSeq(compactedMessages, LAMBDA i: i # Nil)

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
    /\ compactorState' = Compactor_In_PhaseTwoUpdateContext
    /\ UNCHANGED <<messages, cursor, otherVars, compactionHorizon, compactedTopicContext, phaseOneResult>>


CompactorPhaseTwoUpdateContext ==
    /\ compactorState = Compactor_In_PhaseTwoUpdateContext
    /\ compactorState' = Compactor_In_PhaseTwoUpdateHorizon
    /\ compactedTopicContext' = MaxCompactedLedgerId(compactedLedgers)
    /\ UNCHANGED <<bookieVars, otherVars, phaseOneResult, compactionHorizon>>

CompactorPhaseTwoUpdateHorizon ==
    /\ compactorState = Compactor_In_PhaseTwoUpdateHorizon
    /\ compactorState' = Compactor_In_PhaseTwoPersistCusror
    /\ compactionHorizon' = phaseOneResult.readPosition
    /\ UNCHANGED <<bookieVars, otherVars, phaseOneResult, compactedTopicContext>>

CompactorPhaseTwoPersistCusror ==
    /\ compactorState = Compactor_In_PhaseTwoPersistCusror
    /\ compactorState' = Compactor_In_PhaseTwoDeleteLedger
    /\ cursor' = [compactionHorizon |-> compactionHorizon, compactedTopicContext |-> compactedTopicContext]
    /\ UNCHANGED <<messages, compactedLedgers, otherVars, phaseOneResult, compactionHorizon, compactedTopicContext>>

CompactorPhaseTwoDeleteLedger ==
    /\ compactorState = Compactor_In_PhaseTwoDeleteLedger
    /\ compactorState' = Compactor_In_PhaseOne
    /\ phaseOneResult' = Nil
    /\ LET
        maxledgerId == MaxCompactedLedgerId(compactedLedgers)
        \* for simplicity, we delete the second to last compacted ledger
        oldCompactedLedgerId == IF maxledgerId = 1 THEN Nil ELSE maxledgerId - 1
       IN
         IF oldCompactedLedgerId = Nil \/ compactedLedgers[oldCompactedLedgerId] = Nil
         THEN UNCHANGED compactedLedgers
         ELSE compactedLedgers' = [compactedLedgers EXCEPT ![oldCompactedLedgerId] = Nil]
    /\ UNCHANGED <<messages, cursor, otherVars, compactedTopicContext, compactionHorizon>>


\* broker crashes, that is compactor crashes
BrokerCrash ==
    /\ crashTimes < MaxCrashTimes
    /\ crashTimes' = crashTimes + 1
    \* reset compactor state and phase one result
    /\ compactorState' = Compactor_In_PhaseOne
    /\ phaseOneResult' = Nil
    \* reload the compaction horizon and compacted topic context from cursor
    /\ IF cursor # Nil
       THEN /\ compactionHorizon' = cursor.compactionHorizon
             /\ compactedTopicContext' = cursor.compactedTopicContext
       \* if the cursor is Nil, we reset the compaction horizon and compacted topic context to 0
       ELSE /\ compactionHorizon' = 0
             /\ compactedTopicContext' = 0
    /\ UNCHANGED <<bookieVars, consumeTimes>>

\* Consumer consumes messages
Consumer ==
    UNCHANGED vars

Init ==
    /\ \/ /\ ModelProducer
          /\ messages = <<>>
       \/ /\ ~ModelProducer
          \* use \in to randomly select a value from the sequences set(functions set).
          /\ messages \in {msgs \in [1..MessageSentLimit -> [id: 1..MessageSentLimit, key: KeySet, value: ValueSet]]:
                                        \A i \in 1..MessageSentLimit: msgs[i].id = i}
    /\ compactedLedgers = [i \in 1..CompactionTimesLimit |-> Nil]
    /\ phaseOneResult = Nil
    /\ compactorState = Compactor_In_PhaseOne
    /\ compactionHorizon = 0
    /\ compactedTopicContext = 0
    /\ crashTimes = 0
    /\ consumeTimes = 0
    /\ cursor = Nil

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    \* The producer send complete
    /\ Len(messages) = MessageSentLimit
    \* The compactor compact complete, the last phase is phase two write(if there are messages to be compacted)
    \* or phase one(if there are no messages to be compacted, but we don't care about this case)
    /\ compactorState = Compactor_In_PhaseTwoWrite
    /\ MaxCompactedLedgerId(compactedLedgers) = CompactionTimesLimit
    \* The consumer consume complete
    /\ ModelConsumer => consumeTimes = ConsumeTimesLimit
    /\ UNCHANGED vars

Next ==
    \* The producer
    \/ /\ ModelProducer
       /\ Producer
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
    \/ Terminating

Spec == Init /\ [][Next]_vars

\* Safety properties
TypeSafe ==
    LET MessageSpace == [id: 1..MessageSentLimit, key: KeySet, value: ValueSet]
    IN
        /\ \A i \in 1..Len(messages): messages[i] \in MessageSpace
        /\ \A i \in 1..CompactionTimesLimit: compactedLedgers[i] # Nil => \A j \in 1..Len(compactedLedgers[i]): compactedLedgers[i][j] \in MessageSpace
        /\ phaseOneResult # Nil =>
                            /\ \A key \in DOMAIN phaseOneResult.latestForKey: phaseOneResult.latestForKey[key] \in 1..Len(messages)
                            /\ phaseOneResult.readPosition \in 1..Len(messages)
        /\ compactorState \in CompactorState
        /\ compactionHorizon \in 0..MessageSentLimit
        /\ compactedTopicContext \in 0..CompactionTimesLimit
        /\ crashTimes \in 0..MaxCrashTimes
        /\ cursor \in [compactionHorizon: 1..MessageSentLimit, compactedTopicContext: 1..CompactionTimesLimit] \cup {Nil}


\* the useless compacted ledger should be deleted, we model deletion as Nil
\* we can use this invariant to reproduce the ledger leak bug, which is not fixed yet
CompactedLedgerLeak == Cardinality({i \in 1..CompactionTimesLimit : compactedLedgers[i] # Nil}) <= 2

\* the messages before the compaction horizon should be available in the compacted ledger.
\* the latest one in messages with the same key should be available in the compacted ledger.
\* the messages after the compaction horizon could be available in the compacted ledger
\* as the compaction horizon may be smaller than actual compaction position.
CompactionHorizonCorrectness ==
    LET
        compactedLedger == compactedLedgers[compactedTopicContext]
        messagesBeforeHorizon == [i \in 1..compactionHorizon |->
                                 IF messages[i].key = NullKey
                                 THEN IF RetainNullKey
                                      THEN messages[i]
                                      ELSE Nil
                                 ELSE messages[i]]
    IN
        \A i \in 1..Len(messagesBeforeHorizon):
            IF messagesBeforeHorizon[i] = Nil
            THEN RetainNullKey => \E j \in 1..Len(compactedLedger): compactedLedger[j] = messagesBeforeHorizon[i]
            ELSE \E j \in 1..Len(compactedLedger):
                /\ compactedLedger[j].key = messagesBeforeHorizon[i].key
                /\ compactedLedger[j].id >= messagesBeforeHorizon[i].id

\* For null key message, we may don't allow it be consumed mulitple times,
\* that is any null key message in compacted ledger should not be appeared in the messages after the compaction horizon.
\* For non-null key message, we may allow it be consumed mulitple times, as we only care about the latest message with the same key.
\* we can use this invariant to reproduce the message duplication bug, which is not fixed yet
DuplicateNullKeyMessage ==
    RetainNullKey /\ compactedTopicContext # 0 =>
        LET
            range == compactionHorizon+1..Len(messages)
            compactedLedger == compactedLedgers[compactedTopicContext]
            messagesAfterHorizon == [i \in range |->
                                     IF messages[i].key = NullKey
                                     THEN IF RetainNullKey
                                          THEN messages[i]
                                          ELSE Nil
                                     ELSE messages[i]]
        IN
            \A i \in 1..Len(compactedLedger):
                compactedLedger[i].key # NullKey \/
                \A j \in range: compactedLedger[i] # messagesAfterHorizon[j]




\* consumer should be able to consume all the compacted messages


\* Liveness properties
Termination == <>(
    /\ Len(messages) = MessageSentLimit
    /\ compactorState = Compactor_In_PhaseTwoWrite
    /\ MaxCompactedLedgerId(compactedLedgers) = CompactionTimesLimit
    /\ ModelConsumer => consumeTimes = ConsumeTimesLimit)

=============================================================================