sig Node {}

sig Member in Node {
    var nxt: lone Member,
    var qnxt: Node -> lone Node,
    var outbox: set Msg
}

one sig Leader in Member {
    var lnext: Node -> lone Node
}

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
    // all messages are in the pending state
    no SentMsg
    no SendingMsg
    all pm : PendingMsg, m : Member | pm in m.outbox implies pm.sndr = m
    // no node is queueing to become a member
    no qnxt

}

pred trans[] {
    stutter[]
}

pred system[] {
    init[]
    always trans[]
}

fact {
    system[]
}

//-------------------------------------------------------------------//

//-------------------------------------------------------------------//

run {
} for 5