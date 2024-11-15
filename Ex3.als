sig Node {
  var outbox: set Msg
}

var sig Member in Node { 
    var nxt: one Node, 
    var qnxt: Node -> lone Node 
}

var one sig Leader in Member {
    var lnxt: Member -> lone Member
}

var sig LQueue in Member {}

sig Msg {
    sndr: Node, 
    var rcvrs: set Node 
}

var sig SentMsg, SendingMsg, PendingMsg in Msg {}

//-------------------------------------------------------------------//


pred init[] {
    // the set of members consists only of the leader
    Member = Leader
    Member.nxt = Member
    no lnxt
    no LQueue
    
    // no node is queueing to become a member
    no qnxt

    // all messages are in the pending state
    no SentMsg
    no SendingMsg
    Msg = PendingMsg
    no PendingMsg.rcvrs
    all pmsg : PendingMsg, n : Node | pmsg.sndr = n iff pmsg in n.outbox
    //all msg : Msg | msg.sndr !in msg.rcvrs
}

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

pred trans[] {
    stutter[]
    or
    (some m : Member, n : Node | memberApplication[m, n])
    or
    (some m : Member, n : Node | memberPromotion[m, n])
    or
    (some l : Leader, m : Member | leaderApplication[l, m])
    or
    (some l : Leader, lq : LQueue | leaderPromotion[l, lq])
    or
    (some m1, m2 : Member | memberExit[m1, m2])
    or
    (some m : Member, n1, n2 : Node | nonMemberExit[m, n1, n2])
    or
    (some l : Leader, m : Member, msg : Msg | broadcastInit[l, m, msg])
    or
    (some m1 : Member, m2 : Member, msg : Msg | redirectMessage[m1, m2, msg])
    or
    (some l : Leader, m : Member, msg : Msg | terminateBroadcast[l, m, msg])
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
    // n is not a member
    n !in Member
    // n1 not in a member queue
    all m_aux : Member | n !in m_aux.^(~(m_aux.qnxt))

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
    // m is not n2
    n2 !in Member
    // n1 is not n2
    n1 != n2
    // n1 not in a member queue
    all m_aux : Member | n1 !in m_aux.^(~(m_aux.qnxt))
    // n2 is the last node of m's member queue
    no n2.~(m.qnxt)

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
    // n is not a member
    n !in Member

    // postconditions
    Member' = Member + n
    nxt' = nxt + (n->m.nxt) - (m->m.nxt) + (m->n)
    qnxt' = qnxt - m->(n->m)

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
    // n1 is not a member
    n1 !in Member
    // n2 is not a member
    n2 !in Member
    // n1 is not n2
    n1 != n2

    // postconditions
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
    no LQueue
    // l is not m
    l != m
    // m has messages to send
    m in PendingMsg.sndr

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
    // m2 is the last node of the leader queue
    no m2.~(l.lnxt)
    // m1 has messages to send
    m1 in PendingMsg.sndr

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
    // no message currently being broadcast
    no SendingMsg
    // l is not lq
    l != lq

    // postconditions
    lnxt' = lnxt - (l->(lq->l))
    LQueue' = LQueue - lq
    Leader' = Leader - l + lq

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
    // no message currently being broadcast
    no SendingMsg
    // l is not lq1
    l != lq1
    // l is not lq2
    l != lq2
    // lq1 is not lq2
    lq1 != lq2

    // postconditions
    LQueue' = LQueue - lq1
    Leader' = Leader - l + lq1
    lq1.lnxt' = l.lnxt - (lq1->l)
    no l.lnxt'

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
pred memberExit[m1 : Member, m2 : Member] {
    // preconditions
    // m1 and m2 are different
    m1 != m2
    // m1 is not the leader
    m1 !in Leader
    // m1 is not in the leader queue
    m1 !in LQueue
    // m1 member queue is empty
    no m1.qnxt
    // m1 has sent all its messages
    no m1.outbox
    // m2 is behind m1
    m2->m1 in nxt

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

pred nonMemberExit[m : Member, n1 : Node, n2 : Node] {
    nonMemberExitAux1[m, n1, n2]
    or
    some n3 : Node | nonMemberExitAux2[m, n1, n2, n3]
}

// case where n1 is the last node in the queue
pred nonMemberExitAux1[m : Member, n1 : Node, n2 : Node] {
    // preconditions
    // n is in m member queue
    (n1->n2) in m.qnxt
    // n1 is not a member
    n1 !in Member
    // n1 is the last node of the member queue
    no n1.~(m.qnxt)

    // postconditions
    qnxt' = qnxt - m->(n1->n2) // without leader application this makes it not work

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
pred nonMemberExitAux2[m : Member, n1 : Node, n2 : Node, n3 : Node] {
    // preconditions
    // n1, n2 points to n1, n1 points to n3
    n2->n1 in m.qnxt
    n1->n3 in m.qnxt
    // n1 and n2 are not members
    n1 !in Member
    n2 !in Member
    // n1, n2 and n3 are different
    n1 != n2
    n1 != n3
    n2 != n3

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


pred broadcastInit[l : Leader, m : Member, msg: Msg] {
    // preconditions
    m != l
    // l points to m
    (l->m) in nxt
    // msg is a pending message
    msg in PendingMsg
    // msg is only in the leader's outbox
    msg in l.outbox

    // postconditions
    PendingMsg' = PendingMsg - msg
    SendingMsg' = SendingMsg + msg
    outbox' = outbox - (l->msg) + (m->msg)
    rcvrs' = rcvrs + (msg->m)

    // frame conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    SentMsg' = SentMsg
    nxt' = nxt
    qnxt' = qnxt
    lnxt' = lnxt
}

// m1 redirects message to m2
pred redirectMessage[m1 : Member, m2 : Member, msg : Msg] {
    // preconditions
    m1 != m2
    // m1 points to m2
    (m1->m2) in nxt
    // m2 isn't the leader
    m2 !in Leader
    // msg is a sending message
    Msg in SendingMsg
    // msg is in m1's outbox
    msg in m1.outbox

    // postconditions
    outbox' = outbox - (m1->msg) + (m2->msg)
    rcvrs' = rcvrs + (msg->m2)

    // frame conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    PendingMsg' = PendingMsg
    SendingMsg' = SendingMsg
    SentMsg' = SentMsg
    nxt' = nxt
    qnxt' = qnxt
    lnxt' = lnxt
}

pred terminateBroadcast[l : Leader, m : Member, msg : Msg] {
    // preconditions
    l != m
    // m points to l
    (m->l) in nxt
    // msg is a sending message
    msg in SendingMsg
    // msg is in m's outbox
    msg in m.outbox

    // postconditions
    SendingMsg' = SendingMsg - msg
    SentMsg' = SentMsg + msg
    outbox' = outbox - (m->msg)

    // frame conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    PendingMsg' = PendingMsg
    rcvrs' = rcvrs
    nxt' = nxt
    qnxt' = qnxt
    lnxt' = lnxt
}


//-------------------------------------------------------------------//


fun visualizeMemberQ[] : Node -> lone Node {
  Member.qnxt
}

fun visualizeLeaderQ[] : Node -> lone Node {
  Leader.lnxt
}


//-------------------------------------------------------------------//


pred topologyValid[] {
    // members form a single ring
    all m1, m2 : Member |
        m2 in m1.^nxt

    // a member may only point to itself if it's the only member 
    (#Member > 1)
    implies
    (no iden & nxt)

    // no back and forth loops 
    (#Member > 2)
    implies
    (nxt != ~nxt)

    // nodes in the leader queue can't point to themselves
    no n1 : Node |
        (n1 -> n1) in Leader.lnxt

    // source nodes in the leader queue are LQueue nodes
    all n1, n2 : Node |
        ((n1 -> n2) in Leader.lnxt)
        implies
        (n1 in LQueue && n2 in Member)

    // every LQueue node is part of the leader queue
    LQueue in Leader.lnxt.univ

    // nodes only appear in the leader queue once
    all m1 : Member | 
        lone m2 : Member | 
        (m2 -> m1) in Leader.lnxt

    // no back and forth loops
    no m1, m2 : Member |
        ((m1 -> m2) in Leader.lnxt &&
        (m2 -> m1) in Leader.lnxt)

    // the leader queue functions as a queue
    all m1, m2 : Member | 
        ((m1 -> m2) in Leader.lnxt)
        implies 
        ((one m3 : Member |
            (m2 -> m3) in Leader.lnxt)
        or
        (m2 in Leader))

    // the leader doesn't point to anything in the leader queue
    no l : Leader |
        l in Leader.lnxt.univ

    // if the leader queue isn't empty then it ends on the leader
    (Leader.lnxt.univ != none)
        implies
        (one m : Member |
            (m -> Leader) in Leader.lnxt)

    // a node is in the leader queue only if it has messages to send
    all lq : LQueue | lq in PendingMsg.sndr

    // nodes in the member queue can't point to themselves
    no n1 : Node |
        (n1 -> n1) in Member.qnxt

    // source nodes in a member queue are not members
    all n : Node |
        (n in Member.qnxt.univ)
        implies
        (n !in Member)

    // each member only has one member queue
    all m : Member |
        lone n : Node |
        (n -> m) in m.qnxt

    // nodes only appear in the member queue once
    all n1 : Node | 
        lone n2 : Node | 
        (n2 -> n1) in Member.qnxt

    // nodes can only appear in one member queue at a time
    all n : Node | 
        lone m : Member | 
            n in m.qnxt.univ

    // the member queue functions as a queue
    all n1, n2 : Node | 
        ((n1 -> n2) in Member.qnxt)
        implies 
        ((one n3 : Node |
            (n2 -> n3) in Member.qnxt)
        or
        (n2 in Member))
}

pred messageValid[] {
    // a message is only in one member's outbox at a time
    all m : Msg |
        lone n : Member |
            m in n.outbox

    // a pending message is only in its sender's outbox
    all p : PendingMsg | 
        p in p.sndr.outbox &&
        no n : (Node - p.sndr) |
            p in n.outbox

    // a pending message can't have been received by any node
    no PendingMsg.rcvrs

    // the Leader is the sender of every sending message
    #SendingMsg > 0
        implies
            Leader = SendingMsg.sndr
    
    // a sending message has been received by at least one node
    all s : SendingMsg |
        some s.rcvrs
        
    // a sending message is in exactly one member's outbox
    all s : SendingMsg |
        one m : Member |
            s in m.outbox

    // a sent message isn't in any member's outbox
    no SentMsg.~outbox

    // a sent message has been received by at least one node
    all s : SentMsg |
        some s.rcvrs
    
    // a message is either pending, sending or sent
    no (PendingMsg & SendingMsg)
    no (PendingMsg & SentMsg)
    no (SendingMsg & SentMsg)

    // the outbox can only contain pending messages of itself and
    // sending messages of the leader
    all m : Msg, n : Node |
        m in n.outbox
        implies
            (m in PendingMsg && m.sndr = n
            or
            m in SendingMsg && m.sndr = Leader)

    // if a node has a message in its outbox that belongs to the leader, then
    // the node is a member and its in the message's receivers
    all m : SendingMsg, n : Node |
        (m.sndr = Leader && m in n.outbox)
        implies
            (n in Member && n in m.rcvrs)

    // nodes cannot receive their own messages
    all m : Msg |
        m.sndr !in m.rcvrs
}

pred valid[] {
    topologyValid[]
    messageValid[]
}


// Valid holds
check {
    always valid[]
}


//-------------------------------------------------------------------//


pred fairness[] {
    fairnessMemberApplication[]
    and
    fairnessMemberPromotion[]
    and
    fairnessLeaderApplication[]
    and
    fairnessLeaderPromotion[]
    and
    fairnessBroadcastInit[]
    and
    fairnessRedirectMessage[]
    and
    fairnessTerminateBroadcast[]
    and
    fairnessRedirectMessage[]
    and
    fairnessTerminateBroadcast[]
}

pred fairnessMemberApplication[] {
    all n1, n2 : Node |
        (eventually always
            (n1 !in Member &&
            n2 in Member &&
            all m_aux : Member | n1 !in m_aux.^(~(m_aux.qnxt))))
            implies (always eventually memberApplication[n2, n1])
}

pred fairnessMemberPromotion[] {
    all n1, n2 : Node |
        (eventually always
            (n1 !in Member &&
            n2 in Member &&
            no n1.~(n2.qnxt)))
            implies (always eventually memberPromotion[n2, n1])
}

pred fairnessLeaderApplication[] {
    all n1, n2 : Node |
        (eventually always
            (n1 in Member &&
            n1 !in LQueue &&
            n2 in Leader &&
            n1 != n2 &&
            n1 in PendingMsg.sndr))
            implies (always eventually leaderApplication[n2, n1])
}

pred fairnessLeaderPromotion[] {
    all n1, n2 : Node |
        (eventually always
            (n1 in LQueue &&
            n2 in Leader &&
            n1 != n2 &&
            no n2.outbox &&
            no SendingMsg))
            implies (always eventually leaderPromotion[n2, n1])
}

pred fairnessBroadcastInit[] {
    all n1, n2 : Node, msg : Msg |
        (eventually always
            (n1 in Leader &&
            n2 in Member &&
            (n1->n2) in nxt &&
            msg in PendingMsg &&
            msg in n1.outbox))
            implies (always eventually broadcastInit[n1, n2, msg])
}

pred fairnessRedirectMessage[] {
    all n1, n2 : Node, msg : Msg |
        (eventually always
            (n1 in Member &&
            n2 in Member &&
            (n1->n2) in nxt &&
            msg in SendingMsg &&
            msg in n1.outbox))
            implies (always eventually redirectMessage[n1, n2, msg])
}

pred fairnessTerminateBroadcast[] {
    all n1, n2 : Node, msg : Msg |
        (eventually always
            (n1 in Member &&
            n2 in Leader &&
            (n1->n2) in nxt &&
            msg in SendingMsg &&
            msg in n1.outbox))
            implies (always eventually terminateBroadcast[n2, n1, msg])
}


//-------------------------------------------------------------------//


pred noExits[] {
    always no m : Member, n1, n2 : Node |
        nonMemberExit[m, n1, n2]

    always no m1, m2 : Member |
        memberExit[m1, m2]
}

// Liveness condition 3.3.(a)
assert broadcastsTerminate {
    (eventually #Member >= 2 && #Msg = 1 && noExits[] && fairness[])
    implies
    eventually Msg = SentMsg
}

// Assertion holds 3.3(a)
check broadcastsTerminate


// Liveness condition 3.4
assert broadcastsTerminateWithExits {
    (eventually #Member >= 2 && #Msg = 1 && fairness[])
    implies
    eventually Msg = SentMsg
}

// Assertion doesn't hold 3.4
// Ex3.png
check broadcastsTerminateWithExits
