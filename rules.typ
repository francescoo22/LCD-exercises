#import "common.typ": *

#let r = prooftree(
    axiom($$),
    axiom($$),
    rule(n:2, label: "", $$),
  )

// ****************** CCS_seq RULES ******************

#let r1 = prooftree(
    axiom(""),
    rule(label: "End-Zero", $0 ended$),
  )

#let r2 = prooftree(
    axiom($P ended$),
    axiom($Q ended$),
    rule(n:2, label: "End-Par", $P|Q ended$),
  )

#let r3 = prooftree(
    axiom($P ended$),
    rule(label: "End-Hide", $P without A ended$),
  )

#let r4 = prooftree(
    axiom($P ended$),
    rule(label: "End-Sub", $P[f] ended$),
  )

#let r5 = prooftree(
    axiom($P ended$),
    rule(label: (left: "End-Const", right: $space fi K def P$), $K ended$),
  )

#let r6 = prooftree(
    axiom($P ended$),
    axiom($Q ended$),
    rule(n:2, label: "End-Seq", $P ; Q ended$),
  )

#let r7 = prooftree(
    axiom($P ->^alpha P'$),
    rule(label: "Seq-L", $P;Q ->^alpha P';Q$),
  )

#let r8 = prooftree(
    axiom($P ended$),
    axiom($Q ->^alpha Q'$),
    rule(n:2, label: "Seq-R", $P;Q ->^alpha Q'$),
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
    rule(label: (left: "Hide", right: $space alpha, overline(alpha) in.not L$), $P without L ->^alpha P' without L$),
  )

#let c7 = prooftree(
    axiom($P ->^alpha P'$),
    rule(label: "Red", $P[f] ->^f(a) P'[f]$),
  )

#let c8 = prooftree(
    axiom($P ->^alpha P'$),
    rule(label: (left: "Const", right: $space K def P$), $K ->^alpha P'$),
  )

// ****************** RULES FOR THE PROOF ******************

#let p1 = prooftree(
    axiom($$),
    rule(label: "Act", $alpha . e(P) atrans e(P)$),
    rule(label: (left: "Hide", right: $alpha != nu "by construction"$), $e(alpha . P) wnu = alpha . e(P) wnu atrans e(P) wnu$),
  )

#let p2 = prooftree(
    axiom($e(P) atrans P''$),
    rule(label: (left: "Const", right: $K_e def e(P)$), $K_e atrans P''$),
    rule(label: (left: "Hide", right: $alpha != nu "by construction"$), $e(K) wnu = K_e wnu atrans P'' wnu$),
  )

#let p3 = prooftree(
    axiom($e(P) wnu atrans P''$),
    rule(label: (left: "Hide", right: $alpha, overline(alpha) in.not L$), $e(P wL) wnu = e(P) wL wnu tilde^"easy to prove" e(P) wnu wL atrans P'' wL$),
  )

#let p4 = prooftree(
    axiom($e(P) atrans P''$),
    rule(label: (left: "Red"), $e(P)[f]->^(f(alpha)) P''[f]$),
    rule(label: (left: "Hide", right: $alpha != nu "by construction"$), $e(P[f]) wnu = e(P)[f] wnu ->^(f(alpha)) P''[f] wnu$),
  )

#let r = prooftree(
    axiom($$),
    axiom($$),
    rule(n:2, label: "", $$),
  )
