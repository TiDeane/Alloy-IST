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


// members form a single ring
fact {
  all m1, m2 : Member |
    m2 in m1.^nxt
}


// a member may only point to itself if it's the only member 
fact {
  // there might be a better way to do this
  #Member > 1
  implies
  (all m : Member |
    m.nxt != m)
}

// no back and forth loops 
fact {
  #Member > 2
  implies
  (nxt != ~nxt)
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

// the leader queue functions as a queue
fact {
  all n1, n2 : Node | 
    (n1 -> n2) in Leader.lnxt
    implies 
    ((one n3 : Node |
      (n2 -> n3) in Leader.lnxt)
    or
    (n2 in Leader))
  
  // Or this?
  /*
  all n1 : Node |
    (n1 in Leader.qnxt.univ)
    implies
    (one n2 : Node |
      n1 -> n2 in Leader.lnxt)
      or
      (n1 in Leader)
  */
}

// the leader is the end of the queue
fact {
  (no n : Node |
    (Leader -> n) in Leader.lnxt)
  &&
  (lone n : Node |
    (n -> Leader) in Leader.lnxt)
}


//-------------------------------------------------------------------//


// nodes in the member queue can't point to themselves
fact {
  no n1 : Node |
    (n1 -> n1) in Member.qnxt
}

// nodes in a member queue are not members
fact {
  all n1, n2 : Node |
    (n1 -> n2) in Member.qnxt
    implies
    (n1 !in Member)

  // Or this?
  /*
  all n : Node |
    (n in Member.qnxt.univ
    implies
    n !in Member)
  */
}

// member queues end in a member
fact {
  all m : Member |
    lone n : Node |
      (n -> m) in m.qnxt
}

// nodes only appear in the member queue once
fact {
  all n1 : Node | 
    lone n2 : Node | 
      (n2 -> n1) in Member.lnxt
}

// nodes can only appear in one member queue at a time
fact {
  all n : Node | 
    lone m : Member | 
      n in m.qnxt.univ
}

// the member queue functions as a queue
fact {
  all n1, n2 : Node | 
    (n1 -> n2) in Member.qnxt
    implies 
    ((one n3 : Node |
      (n2 -> n3) in Member.qnxt)
    or
    (n2 in Member))
  
  // Or this?
  /*
  all n1 : Node |
  (n1 in Member.qnxt.univ
  implies
  (one n2 : Node |
    n1 -> n2 in Member.qnxt)
    or
    (n1 in Member))
  */
}

// TODO: remove this at the end
// for debugging: two member queues have two non-member nodes
fact {
  some m1, m2 : Member |
    m1 != m2 &&
    some n1, n2 : Node - Member |
      n1 != n2 &&
      (n1 -> n2) in m1.qnxt &&
      (n2 -> m1) in m1.qnxt &&

    some n3, n4 : Node - Member |
      n3 != n4 &&
      (n3 -> n4) in m2.qnxt &&
      (n4 -> m2) in m2.qnxt
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
  no PendingMsg.rcvrs
}

// a sent message isn't in any member's outbox
fact {
  no s : SentMsg |
    s in Member.outbox
  
  // no SentMsg.~outbox ?
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


//TODO: for the visualization, two members should have non-empty member queues
// currently we have a fact that guarantees two members have members queues
// with at least two non-members, but it is for debugging and should be removed
// later on


run {#Node >= 5
     #LQueue >= 1
     #SentMsg >= 1
     #SendingMsg >= 1
     #PendingMsg >= 1}
     for 8