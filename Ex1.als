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

abstract sig Msg {
  sndr: Node, 
  rcvrs: set Node 
}

sig SentMsg, SendingMsg, PendingMsg extends Msg {}


//-------------------------------------------------------------------//


// members form a single ring
fact {
  all m1, m2 : Member |
    m2 in m1.^nxt
}


// a member may only point to itself if it's the only member 
fact {
  (#Member > 1)
  implies
  (no iden & nxt)
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

// source nodes in the leader queue are LQueue nodes
fact {
  all n1, n2 : Node |
    ((n1 -> n2) in Leader.lnxt)
    implies
    (n1 in LQueue && n2 in Member)
}

// every LQueue node is part of the leader queue
fact {
  LQueue in Leader.lnxt.univ
}

// nodes only appear in the leader queue once
fact {
  all m1 : Member | 
    lone m2 : Member | 
      (m2 -> m1) in Leader.lnxt
}

// no back and forth loops
fact {
  no m1, m2 : Member |
    ((m1 -> m2) in Leader.lnxt &&
    (m2 -> m1) in Leader.lnxt)
}

// the leader queue functions as a queue
fact {
  all m1, m2 : Member | 
    ((m1 -> m2) in Leader.lnxt)
    implies 
      ((one m3 : Member |
        (m2 -> m3) in Leader.lnxt)
      or
      (m2 in Leader))
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
  (one m : Member |
    (m -> Leader) in Leader.lnxt)
}

// a node is in the leader queue only if it has messages to send
fact {
  all lq : LQueue | lq in PendingMsg.sndr
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

// each member only has one member queue
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

// the Leader is the sender of every sending message
fact {
  Leader = SendingMsg.sndr 
}

  // a sending message has been received by at least one node
  fact {
    all s : SendingMsg |
      some n : Node |
        n in s.rcvrs
  }

// a sending message is in at least one member's outbox
fact {
  all s : SendingMsg |
    one m : Member |
      s in m.outbox
}

// a sent message isn't in any member's outbox
fact {
  no SentMsg.~outbox
}

// a sent message has been received by at least one node
fact {
  all s : SentMsg |
    some n : Node |
      n in s.rcvrs
}

// the outbox can only contain pending messages of itself and
// sending messages of the leader
fact {
  all m : Msg, n : Node |
    m in n.outbox
    implies
      (m in PendingMsg && m.sndr = n
      or
      m in SendingMsg && m.sndr = Leader)
}

// if a node has a message in its outbox that belongs to the leader, then
// the node is a member and its in the message's receivers
fact {
  all m : SendingMsg, n : Node |
    (m.sndr = Leader && m in n.outbox)
    implies
        (n in Member && n in m.rcvrs)
}

// nodes cannot receive their own messages
fact {
  all m : Msg |
    m.sndr !in m.rcvrs
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