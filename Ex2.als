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
    Msg = PendingMsg
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
    // m is not n
    m != n
    // n1 not in a member queue
    all m_aux : Member, n_aux : Node | m_aux->(n->n_aux) !in qnxt

    // postconditions
    qnxt' = qnxt + m->(n->m)

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
    // m is not n1
    m != n1
    // m is not n2
    m != n2
    // n1 is not n2
    n1 != n2
    // n1 not in a member queue
    all m_aux : Member, n_aux : Node | m_aux->(n1->n_aux) !in qnxt

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
    // n in m member queue and is the first one
    m.qnxt = n->m
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
    // n in m member queue and is the first one, n2 points to n1
    n1->m in m.qnxt
    n2->n1 in m.qnxt
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

}

// case where leader queue is empty
pred leaderApplicationAux1[l : Leader, m : Member] {
    // preconditions
    // l leader queue is empty
    no lnxt
    // l is not m
    l != m
}

pred leaderApplicationAux2[l : Leader, m1 : Member, m2 : Member] {

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

fun visualizeMemberQ[] : Node -> lone Node {
  Member.qnxt
}

run {
    //trace1[]
    //trace2[]
    trace3[]
    trace4[]
    //#Node = 3
} for 5