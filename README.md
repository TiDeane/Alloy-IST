# Alloy-IST

In this project, we use Alloy to model a simple broadcast protocol, referred to as **OneAtATime**. The goal of **OneAtATime** is to allow each of the participants of the protocol, referred to as _members_, to send messages to all other members with the restriction that only one member can send messages at a time. We refer to the member that can send messages as the _leader_.

In order to facilitate message broadcast and membership management, the protocol ensures that node networks are organised in topologies such as the one illustrated below:

![image](https://github.com/user-attachments/assets/b75202dd-b4a3-45f5-bb0c-1153e8b7d22b)

We were given detailed information on the protocol's topological structure, topological constraints, message broadcasting rules, and message-consistency constraints.

Solutions that require a system trace or configuration are illustrated under ``/images``. Solution code for each exercise is under ``Ex1.als``, ``Ex2.als`` and ``Ex3.als``.

## Exercise 1: Static Modelling of OneAtATime Networks and Messages

Given the following partial static Alloy specification designed to describe the structure of valid OneAtATime networks:

```
sig Node {
  outbox: set Msg
}

sig Member in Node {
  nxt: one Node,
  qnxt : Node -> lone Node
}

one sig Leader in Member {
  lnxt: Member -> lone Member
}

sig LQueue in Member {}

sig Msg {
  sndr: Node,
  rcvrs: set Node
}

sig SentMsg, SendingMsg, PendingMsg in Msg {}
```

We were tasked with:

1. Extending the provided static Alloy specification with the topological and message-consistency constraints required to ensure that it only describes valid networks. Each fact of the specification is preceded by a comment describing the constraint that it is intended to model.
2. Using Alloy to generate two different network configurations. Both generated network configurations have: **(1)** at least five nodes; **(2)** a non-empty leader queue; **(3)** at least two non-empty member queues; and **(4)** at least one message of each type of message state (i.e., one pending, one sending, and one sent). We applied an Alloy theme to the generated model so as to guarantee that its presentation is consistent with the one used in the figure above. In particular, the only arrows to be displayed are those corresponding to: the main ring, the leader queue, and the member queues.

## Exercise 2: Dynamic Modelling of OneAtATime Networks and Messages

1. Specify the dynamic system that describes the functioning of the OneAtATime protocol, including:
    - A predicate _init_ describing the initial conditions of the protocol. Assume that in the beginning: **(1)** the set of members consists only of the leader; **(2)** all messages are in the pending state; and **(3)** no node is queueing to become a member.
    - State transformers for all network management operations: leader application, leader promotion, member application, member promotion, member exit, and non-member exit.
    - State transformers for all message routing operations: broadcast initialisation, message redirect, and broadcast termination.
    - Predicates stutter, trans, and system describing the whole behaviour of the system following the approach studied in the lectures.
2. Use Alloy to generate two system traces that illustrate the execution of the protocol. Both generated traces should have at least: **(1)** five nodes; **(2)** one leader promotion; **(3)** one member promotion; **(4)** one member exit; **(5)** one non-member exit; and **(6)** one complete message broadcast (i.e., a message that goes through the three message states: pending, sending, and sent).

## Exercise 3: Verifying Properties of the OneAtATime Protocol

1. Define a predicate valid that captures the topological and message-consistency constraints that valid networks must satisfy. Using this predicate, check that the dynamic system defined in Exercise 2 always maintains network validity.
2. Define a predicate fairness that establishes the fairness conditions of the OneAtATime protocol. Essentially, every node should be able to join a member queue, become a member, become a leader, and send its messages.
3. Using the fairness predicate, model and check the following liveness property of OneAtATime: in a network with at least two nodes, under fairness conditions and if no exit operations
are performed (both member exit and non-member exit), then all message broadcasts terminate.
4. Consider the following variation of property 3.a: in a network with at least two nodes, under fairness conditions, all message broadcasts terminate. Use Alloy to generate a trace that disproves this property.
