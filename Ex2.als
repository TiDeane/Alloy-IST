sig Node {}

sig Member in Node {
    var nxt: lone Member,
    var qnxt: Node -> lone Node,
    var outbox: set Msg
}

one sig Leader in Member {
    var lnext: Node -> lone Node
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

pred stutter[] {
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    lnext' = lnext
}

pred init[] {
    // the set of members consists only of the leader
    Member = Leader
    no lnext
    // all messages are in the pending state
    no SentMsg
    no SendingMsg
    all pmsg : PendingMsg, m : Member | pmsg.sndr = m implies pmsg in m.outbox
    all msg : Msg | msg.sndr !in msg.rcvrs
    // no node is queueing to become a member
    no qnxt
}

pred trans[] {
    stutter[]
    or
    some m : Member, n : Node | memberApplication[m, n]
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
    // m'.qnxt = m.qnxt + (n->m)

    // frame conditions
    nxt' = nxt
    outbox' = outbox
    lnext' = lnext
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
    nxt' = nxt
    outbox' = outbox
    lnext' = lnext
}

//-------------------------------------------------------------------//

pred trace1[] {
    eventually some m : Member, n : Node | memberApplicationAux1[m, n]
}
pred trace2[] {
    eventually some m : Member, n1, n2 : Node | memberApplicationAux2[m, n1, n2]
}

fun visualizeMemberQ[] : Node -> lone Node {
  Member.qnxt
}

run {
    //trace1[]
    trace2[]
    //#Node = 3
} for 5