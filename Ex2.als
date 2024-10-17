sig Node {
    var outbox: set Msg
}

var sig Member in Node {
    var nxt: one Member,
    var qnxt: Node -> lone Node,
}

var one sig Leader in Member {
    var lnxt: Node -> lone Node
}

var sig LQueue in Member {}

abstract sig Msg {
    sndr: Node,
    var rcvrs: set Node
}

var sig SentMsg, SendingMsg, PendingMsg in Msg {}

//-------------------------------------------------------------------//

pred stutter[] {
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
    outbox' = outbox
    nxt' = nxt
    qnxt' = qnxt
    lnxt' = lnxt
    rcvrs' = rcvrs
}

pred init[] {
    // the set of members consists only of the leader
    Member = Leader
    Member.nxt = Member
    no lnxt
    no LQueue

    // all messages are in the pending state
    no SentMsg
    no SendingMsg
    Msg = PendingMsg // maybe uneeded, because Msg is abstract and we have "no" on the other two
    no PendingMsg.rcvrs
    all pmsg : PendingMsg, n : Node | pmsg.sndr = n iff pmsg in n.outbox
    //all msg : Msg | msg.sndr !in msg.rcvrs
    
    // no node is queueing to become a member
    no qnxt
}

pred trans[] {
    stutter[]
    or
    some m : Member, n : Node | memberApplication[m, n]
    or
    some m : Member, n : Node | memberPromotion[m, n]
    or
    some l : Leader, m : Member | leaderApplication[l, m]
    or
    some l : Leader, lq : LQueue | leaderPromotion[l, lq]
    or
    some m1, m2 : Member | memberExit[m1, m2]
    or
    some m : Member, n : Node | nonMemberExit[m, n]
}

pred system[] {
    init[]
    and
    always trans[]
}

fact {
    system[]
}

//-------------------------------------------------------------------//

pred memberApplication[m : Member, n : Node] {
    //m = Leader // to remove
    memberApplicationAux1[m, n]
    or
    some n2 : Node | memberApplicationAux2[m, n, n2]
}

// case where m member queue is empty
pred memberApplicationAux1[m : Member, n : Node] {
    // preconditions
    // m member queue is empty
    no m.qnxt
    // n is not a member
    n !in Member
    // m is not n
    m != n
    // n1 not in a member queue
    all m_aux : Member, n_aux : Node | m_aux->(n->n_aux) !in qnxt

    // postconditions
    qnxt' = qnxt + (m->(n->m))

    // frame conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
    outbox' = outbox
    nxt' = nxt
    lnxt' = lnxt
    rcvrs' = rcvrs
}

// case where m member queue is not empty
pred memberApplicationAux2[m : Member, n1 : Node, n2 : Node] {
    // preconditions
    // m member queue contains n2
    n2 in m.^(~(m.qnxt))
    // n is not a member
    n1 !in Member
    // m is not n1
    m != n1
    // m is not n2
    m != n2
    // n1 is not n2
    n1 != n2
    // n1 not in a member queue
    all m_aux : Member, n_aux : Node | m_aux->(n1->n_aux) !in qnxt
    // I think we still need a constraint that certifies n2 is the last node in the queue

    // postconditions
    qnxt' = qnxt + (m->(n1->n2))

    // frame conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
    outbox' = outbox
    nxt' = nxt
    lnxt' = lnxt
    rcvrs' = rcvrs
}

pred memberPromotion[m : Member, n : Node] {
    memberPromotionAux1[m, n]
    or
    some n2 : Node | memberPromotionAux2[m, n, n2]
}

// case where n is the only node in the queue
pred memberPromotionAux1[m : Member, n : Node] {
    // preconditions
    // n is the only node in the m member queue
    m.qnxt = n->m
    // n is not m (Maybe uneeded?)
    n != m

    // postconditions
    Member' = Member + n
    nxt' = nxt + (n->m.nxt) - (m->m.nxt) + (m->n)
    qnxt' = qnxt - m->(n->m)
    // o stor quando estava a explicar usou: no m.qnxt'
    // se meter só isto, consigo que garantir que o resto
    // dos qnxt não se alteram?

    // frame conditions
    Leader' = Leader
    LQueue' = LQueue
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
    outbox' = outbox
    lnxt' = lnxt
    rcvrs' = rcvrs
}

// case where n1 is the head of the member queue and n2 points to n1
pred memberPromotionAux2[m : Member, n1 : Node, n2 : Node] {
    // preconditions
    // n1 in m member queue and is the first one, n2 points to n1
    n1->m in m.qnxt
    n2->n1 in m.qnxt
    // these 3 are probably uneeded?
    // m is not n1
    m != n1
    // m is not n2
    m != n2
    // n1 is not n2
    n1 != n2

    // postconditions
    //m.qnxt' = m.qnxt - (n1->m) - (n2->n1) + (n2->n1) // mesmo caso que em cima
    qnxt' = qnxt - m->(n1->m) - m->(n2->n1) + m->(n2->m)
    Member' = Member + n1
    nxt' = nxt + (n1->m.nxt) - (m->m.nxt) + (m->n1)

    // frame conditions
    Leader' = Leader
    LQueue' = LQueue
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
    outbox' = outbox
    lnxt' = lnxt
    rcvrs' = rcvrs
}

pred leaderApplication[l : Leader, m : Member] {
    leaderApplicationAux1[l, m]
    or
    some m2 : Member | leaderApplicationAux2[l, m, m2]
}

// case where leader queue is empty
pred leaderApplicationAux1[l : Leader, m : Member] {
    // preconditions
    // leader queue is empty
    no lnxt
    // or no LQueue?
    // m not in the leader queue // probably uneeded since LQueue is empty
    m !in LQueue
    // l is not m
    l != m

    // postconditions
    lnxt' = lnxt + (l->(m->l))
    LQueue' = LQueue + m

    // frame conditions
    Member' = Member
    Leader' = Leader
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
    outbox' = outbox
    nxt' = nxt
    qnxt' = qnxt
    rcvrs' = rcvrs
}

// case where leader queue is not empty
pred leaderApplicationAux2[l : Leader, m1 : Member, m2 : Member] {
    // preconditions
    // leader queue contains m2
    m2 in LQueue
    // m1 not in the leader queue
    m1 !in LQueue
    // l is not m1
    l != m1
    // l is not m2
    l != m2
    // m1 is not m2
    m1 != m2
    // (Same as MAppAux2) I think we still need a constraint that certifies m2 is the last node in the queue


    // postconditions
    lnxt' = lnxt + (l->(m1->m2))
    LQueue' = LQueue + m1

    // frame conditions
    Member' = Member
    Leader' = Leader
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
    outbox' = outbox
    nxt' = nxt
    qnxt' = qnxt
    rcvrs' = rcvrs
}

pred leaderPromotion[l : Leader, lq : LQueue] {
    leaderPromotionAux1[l, lq]
    or
    some lq2 : LQueue | leaderPromotionAux2[l, lq, lq2]
}

// case where lq is the only node in the leader queue
pred leaderPromotionAux1[l : Leader, lq : LQueue ] {
    // preconditions
    // lq is the only member in leader queue
    LQueue = lq
    // leader has sent all its messages
    no l.outbox
    // l is not lq
    l != lq

    // postconditions
    lnxt' = lnxt - (l->(lq->l)) // or " no lnxt' " ?
    LQueue' = LQueue - lq
    Leader' = Leader - l + lq // could we just put "Leader' = l"?

    // frame conditions
    Member' = Member
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
    outbox' = outbox
    nxt' = nxt
    qnxt' = qnxt
    rcvrs' = rcvrs
}

// case where lq1 is the head of the leader queue and lq2 points to lq1
pred leaderPromotionAux2[l : Leader, lq1 : LQueue, lq2 : LQueue] {
    // preconditions
    // lq1 in leader queue and is the head, lq2 points to lq1
    lq1->l in l.lnxt
    lq2->lq1 in l.lnxt
    // leader has sent all its messages
    no l.outbox
    // these 3 are probably uneeded?
    // l is not lq1
    l != lq1
    // l is not lq2
    l != lq2
    // lq1 is not lq2
    lq1 != lq2

    // postconditions
    LQueue' = LQueue - lq1
    Leader' = Leader - l + lq1 // could we just put "Leader' = l"?
    lq1.lnxt' = l.lnxt - (lq1->l)
    no l.lnxt'
    // used here the same logic as the member queue
    // but I'm not sure what the teacher means with
    // "the tail of the old leader's queue becomes
    // the new leader's queue"

    // frame conditions
    Member' = Member
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
    outbox' = outbox
    nxt' = nxt
    qnxt' = qnxt
    rcvrs' = rcvrs
}

// m1 wants to exit, m2.nxt = m1 (m2 will always exists because the Leader can't leave)
// TODO: this doesn't work with only 2 nodes right now
pred memberExit[m1 : Member, m2 : Member] {
    // preconditions
    // m1 is not the leader
    m1 !in Leader
    // m1 is not in the leader queue
    m1 !in LQueue
    // m1 member queue is empty
    no m1.qnxt
    // m1 has sent all its messages
    no m1.outbox
    // m2 is behind m1
    m2->m1 in nxt // or "m2.nxt->m1" ?

    // postconditions
    nxt' = nxt - (m2->m1) + (m2->m1.nxt) - (m1->m1.nxt)
    Member' = Member - m1

    // frame conditions 
    Leader' = Leader
    LQueue' = LQueue
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
    outbox' = outbox
    qnxt' = qnxt
    lnxt' = lnxt
    rcvrs' = rcvrs
}

// this is wrong, the cases are not these ones
// I think it should be: when n is last and when n is in the middle
pred nonMemberExit[m : Member, n : Node] {
    nonMemberExitAux1[m, n]
    or
    some n2, n3 : Node | nonMemberExitAux2[m, n, n2, n3]
}

// case where n is the only node in the queue
pred nonMemberExitAux1[m : Member, n : Node] {
    // preconditions
    // n is the only node in the m member queue
    m.qnxt = n->m
    // n is not m (Maybe uneeded?)
    n != m

    // postconditions
    qnxt' = qnxt - (m->(n->m))

    // frame conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
    outbox' = outbox
    nxt' = nxt
    lnxt' = lnxt
    rcvrs' = rcvrs
}

// case where n1 wants to exit, n2 point to n1, n1 points to n3
// TODO: does not work
pred nonMemberExitAux2[m : Member, n1 : Node, n2 : Node, n3 : Node] {
    // preconditions
    // n1, n2 points to n1, n1 points to n3
    n1->n3 in m.qnxt
    n2->n1 in m.qnxt

    // postconditions
    qnxt' = qnxt - m->(n2->n1) + m->(n2->n3) - m->(n1->n3)

    // frame conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
    outbox' = outbox
    nxt' = nxt
    lnxt' = lnxt
    rcvrs' = rcvrs
}

//-------------------------------------------------------------------//

pred trace1[] {
    eventually some m : Member, n : Node | memberApplicationAux1[m, n]
}
pred trace2[] {
    eventually some m : Member, n1, n2 : Node | memberApplicationAux2[m, n1, n2]
}

pred trace3[] {
    eventually some m : Member, n : Node | memberPromotionAux1[m, n]
}

pred trace4[] {
    eventually some m : Member, n1, n2 : Node | memberPromotionAux2[m, n1, n2]
}

pred trace5[] {
    eventually some l : Leader, m : Member | leaderApplicationAux1[l, m]
}

pred trace6[] {
    eventually some l : Leader, m1, m2 : Member | leaderApplicationAux2[l, m1, m2]
}

pred trace7[] {
    eventually some l : Leader, lq : LQueue | leaderPromotionAux1[l, lq]
}

pred trace8[] {
    eventually some l : Leader, lq1, lq2 : LQueue | leaderPromotionAux2[l, lq1, lq2]
}

pred trace9[] {
    eventually some m1, m2 : Member | memberExit[m1, m2]
}

pred trace10[] {
    eventually some m : Member, n : Node | nonMemberExitAux1[m, n]
}

pred trace11[] {
    eventually some m : Member, n1, n2, n3 : Node | nonMemberExitAux2[m, n1, n2, n3]
}

fun visualizeMemberQ[] : Node -> lone Node {
  Member.qnxt
}

fun visualizeLeaderQ[] : Node -> lone Node {
  Leader.lnxt
}

run {
    //trace1[]
    //trace2[]
    //trace3[]
    //trace4[]
    //trace5[]
    //trace6[]
    //trace7[]
    //trace8[]
    //trace9[]
    //trace10[]
    trace11[]
    //#Node = 2
} for 5