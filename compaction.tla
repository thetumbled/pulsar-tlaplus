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
          RetainNullKey \* whether retains null key message in compacted ledger

ASSUME /\ MessageSentLimit \in Nat
       /\ CompactionTimesLimit \in Nat
       /\ ModelConsumer \in BOOLEAN
       /\ ConsumeTimesLimit \in Nat
       /\ KeySpace \in SUBSET Nat
       /\ ValueSpace \in SUBSET Nat
       /\ RetainNullKey \in BOOLEAN

\* Model values
CONSTANTS Nil, \* The nil value
          Compactor_In_PhaseOne, \* The compactor is in phase one
          Compactor_In_PhaseTwoWrite, \* The compactor is in phase two write
          Compactor_In_PhaseTwoAck \* The compactor is in phase two ack

NullKey == 0 \* The nil key
NullValue == 0 \* The nil value
KeySet == KeySpace \cup {NullKey} \* The key set, 0 is reserved for the nil key
ValueSet == ValueSpace \cup {NullValue} \* The value set, 0 is reserved for the nil value

CompactorState == {Compactor_In_PhaseOne, Compactor_In_PhaseTwoWrite, Compactor_In_PhaseTwoAck} \* The state of the compactor

VARIABLES messages, \* bookkeeping the messages, queue of messages
          compactedLedgers,  \* bookkeeping the compacted messages,
                             \* mapping from the compacted ledger id to the original message queue
          compactorState,    \* the state of the compactor
          phaseOneResult     \* the result of phase one compaction, model Map<String, MessageId> latestForKey


compactorVars == <<phaseOneResult, compactorState>>
vars == <<messages, compactedLedgers, compactorVars>>


\* producer sends messages
\* may be we could replace the producer with pre-defined messages to minimize the state space
ConstructMessage(inputKey, inputValue) ==
    [key |-> inputKey, value |-> inputValue]

Producer ==
    /\ Len(messages) < MessageSentLimit
    /\ \E inputKey \in KeySet, inputValue \in ValueSet:
        messages' = Append(messages, ConstructMessage(inputKey, inputValue))
    /\ UNCHANGED <<compactedLedgers, compactorVars>>


\* compactor compacts messages
GetKeys(messages) == {messages[i].key : i \in 1..Len(messages)} \ {NullKey}
CompactorPhaseOne ==
    /\ compactorState = Compactor_In_PhaseOne
    /\ phaseOneResult = Nil
    /\ phaseOneResult' = [key \in GetKeys(messages) |-> Max({i \in 1..Len(messages) : messages[i].key = key})]
    /\ compactorState' = Compactor_In_PhaseTwoWrite
    /\ UNCHANGED <<messages, compactedLedgers>>

\* create a new compacted ledger and compact the messages
GetNewLedgerId(compactedLedgers) == Max({i \in 1..CompactionTimesLimit : compactedLedgers[i] # Nil}) + 1
CompactMessages(messages, phaseOneResult) ==
    LET
        compactedMessages == [i \in 1..Len(messages) |->
                                IF messages[i].key = NullKey
                                THEN IF RetainNullKey
                                     THEN messages[i]
                                     ELSE Nil
                                ELSE IF i = phaseOneResult[messages[i].key]
                                     THEN messages[i]
                                     ELSE Nil]
        ValidIndex == {i \in 1..Len(compactedMessages) : compactedMessages[i] # Nil}
    IN
        \* filter out the nil messages
        [i \in ValidIndex |-> compactedMessages[i]]

CompactorPhaseTwoWrite ==
    /\ phaseOneResult # Nil
    /\ compactorState = Compactor_In_PhaseTwoWrite
    /\ LET
        ledgerId == GetNewLedgerId(compactedLedgers)
        compactedMessages == CompactMessages(messages, phaseOneResult)
       IN
        /\ ledgerId \in 1..CompactionTimesLimit
        /\ compactedLedgers' = [compactedLedgers EXCEPT ![ledgerId] = compactedMessages]
    /\ phaseOneResult' = Nil
    /\ compactorState' = Compactor_In_PhaseTwoAck
    /\ UNCHANGED <<messages>>




Init ==
    /\ messages = <<>>
    /\ compactedLedgers = [i \in 1..CompactionTimesLimit |-> Nil]
    /\ phaseOneResult = Nil
    /\ compactorState = Compactor_In_PhaseOne

Next ==
    \* The producer
    \/ Producer
    \* The compactor
    \/ CompactorPhaseOne
    \/ CompactorPhaseTwoWrite
    \* The consumer
    \/ /\ ModelConsumer
       /\ Consumer


=============================================================================