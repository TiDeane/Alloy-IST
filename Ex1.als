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

// members form a ring
fact {
  all m : Member |
    m in m.^nxt
}

// member may only point to itself if it's the only member
fact {
  all m : Member |
    #Member > 1
    implies 
    m.nxt != m
}

fact {
  #Member > 1 implies nxt != ~nxt
}


run { #Member = 3 } for 3