sig Node {}

sig Member in Node {
  nxt: lone Member,
  qnxt : Node -> lone Node,
  outbox: set Msg
}

one sig Leader in Member {
  lnxt: Node -> lone Node
}

sig LQueue in Member {}

abstract sig Msg {
  sndr: Node,
  rcvrs: set Node
}

sig SentMsg extends Msg {}

sig SendingMsg extends Msg {}

sig PendingMsg extends Msg {}


//-------------------------------------------------------------------//


// members form a ring
fact {
  all m1, m2 : Member |
    m2 in m1.^nxt
}


// a member may only point to itself if it's the only member 
fact {
  // should #Member > 1 be inside or outside the "all" ?
  #Member > 1 implies
  (all m : Member |
    m.nxt != m)
}

// no back and forth loops 
fact {
  // should #Member > 1 be inside or outside the "all" ?
  #Member > 1 implies
  (all m : Member |
    m.nxt != m.~nxt)
  // why is this different from (#Member > 1 implies nxt != ~nxt) ?
}


//-------------------------------------------------------------------//


// nodes in the leader queue are Members and LQueue
fact {
  all n1, n2 : Node |
    (n1 -> n2) in Leader.lnxt
    implies
    (n1 in LQueue && n2 in Member)
}

// every LQueue node is part of the leader queue
fact {
  all lq : LQueue |
    one n : Node |
      (lq -> n) in Leader.lnxt
}

// nodes only appear in the leader queue once
fact {
  all n1 : Node | 
    lone n2 : Node | 
      (n2 -> n1) in Leader.lnxt
}

// nodes in the leader queue can't point to themselves
fact {
  no n1 : Node |
    (n1 -> n1) in Leader.lnxt
}

// no back and forth loops
fact {
  no n1, n2 : Node |
    ((n1 -> n2) in Leader.lnxt &&
    (n2 -> n1) in Leader.lnxt)
}

// the leader queue functions as a queue (maybe a better name for this fact?)
fact {
  all n1, n2 : Node | 
    (n1 -> n2) in Leader.lnxt implies 
      ((one n3 : Node |
        (n2 -> n3) in Leader.lnxt)
      ||
      (n2 in Leader))
}

// the leader is the end of the queue
fact {
  (no n : Node |
    (Leader -> n) in Leader.lnxt)
  &&
  (one n : Node |
    (n -> Leader) in Leader.lnxt)
}


//-------------------------------------------------------------------//


// nodes in a member queue are not members
fact {
  //TODO
}

// member queues end in the corresponding member
fact {
  //TODO
}

// nodes only appear in the member queue once
fact {
  //TODO
}

// nodes can only appear in one member queue at a time
fact {
  //TODO
}

// at least two members have non-empty member queues
// note: I think this shouldn't be a fact, and instead should be
// part of the run command
fact {
  some m1, m2 : Member | 
    m1 != m2 && 
    some m1.qnxt &&
    some m2.qnxt
}


//-------------------------------------------------------------------//


// a message is only in one member's outbox at a time
fact {
  all m : Msg |
    lone n : Member |
      m in n.outbox
}

// a pending message is only in its sender's outbox
fact {
  all p : PendingMsg | 
    p in p.sndr.outbox &&
    no n : (Node - p.sndr) |
      p in n.outbox
}

// a pending message can't have been received by any node
fact {
  all p : PendingMsg |
    p.rcvrs = none
  // why is this different from "no PendingMsg.rcvrs" ?
}

// a sent message isn't in any member's outbox
fact {
  all s : SentMsg |
    no m : Member |
      s in m.outbox
}

// note: intuitively, a sent message has been received by every member...
// but considering nodes can stop being members, there can be static states
// where a non member received a SentMsg and a (new) member didn't


//-------------------------------------------------------------------//

fun visualizeMemberQ[] : Node -> lone Node {
  Member.qnxt
}

fun visualizeLeaderQ[] : Node -> lone Node {
  Leader.lnxt
}


run {#Node >= 5
     #LQueue >= 1
     #SentMsg >= 1
     #SendingMsg >= 1
     #PendingMsg >= 1}
     for 8