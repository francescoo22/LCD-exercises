#import "common.typ": *

#let r = prooftree(
    axiom($$),
    axiom($$),
    rule(n:2, label: "", $$),
  )

// ****************** MY RULES ******************

#let r1 = prooftree(
    axiom(""),
    rule(label: "End-Zero", $0 ->^nu$),
  )

#let r2 = prooftree(
    axiom($P ended$),
    axiom($Q->^nu$),
    rule(n:2, label: "End-Par", $P|Q ->^nu$),
  )

#let r3 = prooftree(
    axiom($P ended$),
    rule(label: "End-Hide", $P without A ->^nu$),
  )

#let r4 = prooftree(
    axiom($P ended$),
    rule(label: "End-Sub", $P[f] ended$),
  )

#let r5 = prooftree(
    axiom($P ended$),
    axiom($K def P$),
    rule(n:2, label: "End-Const", $K ended$),
  )

#let r6 = prooftree(
    axiom($P ended$),
    axiom($Q ended$),
    rule(n:2, label: "End-Plus", $P + Q ended$),
  )

#let r7 = prooftree(
    axiom($P ended$),
    axiom($Q ->^alpha Q'$),
    rule(n:2, label: "Comp", $P;Q ->^alpha Q'$),
  )

#let r8 = prooftree(
    axiom($forall i in I . P_i ended$),
    rule(label: "End-Sum", $sum_(i in I) P_i ended$),
  )

// ****************** CLASSIC RULES ******************

#let c1 = prooftree(
    axiom($$),
    rule(label: "Act", $alpha . P ->^alpha P$),
  )

#let c2 = prooftree(
    axiom($P_j ->^alpha P_j '$),
    rule(label: (left: "Sum", right: $space j in I$), $sum_(i in I) P_i ->^alpha P_j '$),
  )

#let c3 = prooftree(
  axiom($P ->^alpha P'$),
  rule(label: "Par-1", $P|Q ->^alpha P'|Q$),
)

#let c4 = prooftree(
  axiom($Q ->^alpha Q'$),
  rule(label: "Par-2", $P|Q ->^alpha P|Q'$),
)

#let c5 = prooftree(
  axiom($P ->^alpha P'$),
  axiom($Q ->^overline(alpha) Q'$),
  rule(n:2, label: "Par-3", $P|Q ->^tau P'|Q'$),
)

#let c6 = prooftree(
    axiom($P ->^alpha P'$),
    rule(label: (left: "Res", right: $space alpha, overline(alpha) in.not L$), $P without L ->^alpha P' without L$),
  )

#let c7 = prooftree(
    axiom($P ->^alpha P'$),
    rule(label: "Red", $P[f] ->^f(a) P'[f]$),
  )

#let c8 = prooftree(
    axiom($P ->^alpha P'$),
    rule(label: (left: "Const", right: $space K def P$), $K ->^alpha P'$),
  )