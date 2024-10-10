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
  all m : Member |
    m in m.^nxt
}

// a member may only point to itself if it's the only member 
fact {
  all m : Member |
    (#Member > 1
    implies 
    m.nxt != m)
}

// no back and forth loops 
fact {
  #Member > 1 implies nxt != ~nxt
}


//-------------------------------------------------------------------//


// nodes in the leader queue are Members and LQueue
fact {
  //TODO
}

// the leader queue ends in the leader
fact {
  //TODO
}

// nodes only appear in the leader queue once
fact {
  //TODO
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
}

// a sent message isn't in any member's outbox
fact {
  all s : SentMsg |
    no m : Member |
      s in m.outbox
}

// note: intuitively, a sent message has been received by every member...
// but considering nodes can stop being members, there can be static states
// where a non member received a SentMsg


//-------------------------------------------------------------------//


run {#Node >= 5
     #LQueue > 0
     #SentMsg >= 1
     #SendingMsg >= 1
     #PendingMsg >= 1}
     for 8