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