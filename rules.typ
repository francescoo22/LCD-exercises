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
    axiom($P atrans P'$),
    rule(label: "Seq-L", $P;Q atrans P';Q$),
  )

#let r8 = prooftree(
    axiom($P ended$),
    axiom($Q atrans Q'$),
    rule(n:2, label: "Seq-R", $P;Q atrans Q'$),
  )

// ****************** CLASSIC RULES ******************

#let c1 = prooftree(
    axiom($$),
    rule(label: "Act", $alpha . P atrans P$),
  )

#let c2 = prooftree(
    axiom($P_j atrans P_j '$),
    rule(label: (left: "Sum", right: $space j in J$), $sum_(j in J) P_j atrans P_j '$),
  )

#let c3 = prooftree(
  axiom($P atrans P'$),
  rule(label: "Par-1", $P|Q atrans P'|Q$),
)

#let c4 = prooftree(
  axiom($Q atrans Q'$),
  rule(label: "Par-2", $P|Q atrans P|Q'$),
)

#let c5 = prooftree(
  axiom($P atrans P'$),
  axiom($Q ->^overline(alpha) Q'$),
  rule(n:2, label: "Par-3", $P|Q ->^tau P'|Q'$),
)

#let c6 = prooftree(
    axiom($P atrans P'$),
    rule(label: (left: "Hide", right: $space alpha, overline(alpha) in.not L$), $P without L atrans P' without L$),
  )

#let c7 = prooftree(
    axiom($P atrans P'$),
    rule(label: "Red", $P[f] ->^f(a) P'[f]$),
  )

#let c8 = prooftree(
    axiom($P atrans P'$),
    rule(label: (left: "Const", right: $space K def P$), $K atrans P'$),
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
    axiom($e(P) wnu atrans P'' wnu$),
    rule(label: (left: "Hide", right: $alpha, overline(alpha) in.not L$), $e(P) wnu wL atrans P'' wnu wL$),
  )

#let p4 = prooftree(
    axiom($e(P) wnu atrans P'' wnu$),
    rule(label: "Red", $e(P) wnu [f] ->^(f(alpha)) P'' wnu [f]$),
  )

#let p5 = prooftree(
    axiom(label: "Act", $alpha_j . P_j ->^(alpha_j) P_j$),
    rule(label: (left: "Sum", right: $space j in J$), $sum_(j in J != emptyset) alpha_j . P_j ->^(alpha_j) P_j$),
)

#let p6 = prooftree(
    axiom(label: "Act", $alpha_j . e(P_j) ->^(alpha_j) e(P_j)$),
    rule(label: (left: "Sum", right: $space j in J$), $sum_(j in J != emptyset) alpha_j . e(P_j) ->^(alpha_j) e(P_j)$),
    rule(label: (left: "Hide", right: $alpha_j != nu$), $e(sum_(j in J != emptyset) alpha_j . P_j) wnu = sum_(j in J != emptyset) alpha_j . e(P_j) wnu ->^(alpha_j) e(P_j) wnu$),
)

#let p7 = prooftree(
    axiom($e(P) atrans P''$),
    rule(label: (left: "Red", right: $alpha != nu => [nu'/nu] (alpha) = alpha$), $e(P)[nu'/nu] atrans P''[nu'/nu]$),
    rule("..."),
    rule(label: "", $e(P | Q) wnu = (e(P)[nu'/nu] | e(Q)[nu'/nu] | overline(nu') . overline(nu') . nu . 0) wnup wnu atrans (P''[nu'/nu] | e(Q)[nu'/nu] | overline(nu') . overline(nu') . nu . 0) wnup wnu$)
  )

#let r = prooftree(
    axiom($$),
    axiom($$),
    rule(n:2, label: "", $$),
  )
