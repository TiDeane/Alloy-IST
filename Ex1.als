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
  (#Member > 1)
  implies
  (all m : Member |
    m.nxt != m)
}

// no back and forth loops 
fact {
  (#Member > 2)
  implies
  (nxt != ~nxt)
}


//-------------------------------------------------------------------//


// nodes in the leader queue can't point to themselves
fact {
  no n1 : Node |
    (n1 -> n1) in Leader.lnxt
}

// source nodes in the leader queue are LQueue and point to Members
fact {
  all n1, n2 : Node |
    ((n1 -> n2) in Leader.lnxt)
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

// no back and forth loops
fact {
  no n1, n2 : Node |
    ((n1 -> n2) in Leader.lnxt &&
    (n2 -> n1) in Leader.lnxt)
}

// the leader queue functions as a queue
fact {
  all n1, n2 : Node | 
    ((n1 -> n2) in Leader.lnxt)
    implies 
      ((one n3 : Node |
        (n2 -> n3) in Leader.lnxt)
      or
      (n2 in Leader))
}

// the leader doesn't point to anything in the leader queue
fact {
  no l : Leader |
    l in Leader.lnxt.univ
}

// if the leader queue isn't empty then it ends on the leader
fact {
  (Leader.lnxt.univ != none)
  implies
  (one n : Node |
    (n -> Leader) in Leader.lnxt)
}


//-------------------------------------------------------------------//


// nodes in the member queue can't point to themselves
fact {
  no n1 : Node |
    (n1 -> n1) in Member.qnxt
}

// source nodes in a member queue are not members
fact {
  all n : Node |
    (n in Member.qnxt.univ)
    implies
    (n !in Member)
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
      (n2 -> n1) in Member.qnxt
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
    ((n1 -> n2) in Member.qnxt)
    implies 
      ((one n3 : Node |
        (n2 -> n3) in Member.qnxt)
      or
      (n2 in Member))
}


//-------------------------------------------------------------------//


// a message is only in one member's outbox at a time
fact {
  all m : Msg |
    lone n : Member |
      m in n.outbox
}

// a pending message isn't waiting to be redirected to the next member
fact {
  no PendingMsg.~outbox
}

// a pending message can't have been received by any node
fact {
  no PendingMsg.rcvrs
}

// a sent message isn't in any member's outbox
fact {
  no SentMsg.~outbox
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

pred trace1[] {
  #Node >= 5
  #LQueue >= 1
  #SentMsg >= 1
  #SendingMsg >= 1
  #PendingMsg >= 1

  // at least two members have non-empty member queues
  some m1, m2 : Member |
    m1 != m2 &&
    some n1, n2 : Node - Member |
      n1 != n2 &&
      (n1 -> m1) in m1.qnxt &&
      (n2 -> m2) in m2.qnxt
}


run { trace1[] } for 8