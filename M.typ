#import "common.typ": *
#import "rules.typ": *

= Exercise M

Discuss an extension of CCS with an operator of sequential composition between processes $P; Q$. Provide an operational semantics and analyze the possibility of having an encoding in CCS of the defined operator.

*Solution*

== $CCS_seq$

$ P, Q ::= K | alpha . P | sum_(i in I) alpha . P_i | (P | Q) | P[f] | P without L | P;Q $

== Operational Semantics

#v(2em)

*Classical rules*

#grid(
  columns: (auto, auto, auto),
  column-gutter: 1fr,
  row-gutter: 2em,
  c1, c2, c3, c4, c5, c6, c7, c8
)

#v(2em)

*$CCS_seq$ rules*

#grid(
  columns: (auto, auto, auto),
  column-gutter: 1fr,
  row-gutter: 2em,
  r1, r2, r3, r4, r5, r6, r7, r8
)

== Encoding

Let $e : CCS_seq -> CCS$

The encoding of a $CCS_seq$ process $P$ is $e(P) without {nu}$

Note: $nu, nu'$ are channels that does not appear in $P$

#list(
  tight: false,
  spacing: 2em,
  $e(0) = nu . 0$,
  $e(alpha . P) = alpha . e(P)$,
  $e(K) = K_e, space K_e def e(P) fi K def P$,
  $e(P | Q) = (e(P)[nu'/nu] | e(Q)[nu'/nu] | overline(nu') . overline(nu') . nu . 0) without {nu'}$,
  $e(sum_(j in J, J != emptyset) alpha_j . P_j) = sum_(j in J, J != emptyset) alpha_j . e(P_j)$,
  $e(P[f]) = e(P) [f]$,
  $e(P without L) = e(P) without L$,
  $e(P; Q) = (e(P)[nu'/nu] | overline(nu') . e(Q)) without {nu'}$
)

== Equivalence

$ forall P in CCS_seq . P approx e(P) wnu $

let $cr = {(P, e(P) wnu) | P in CCS_seq} union approx$

*TODO se aggiungo cose a $cr$ vanno dimostrate*
we need to prove that $cr$ is a weak bisimulation i.e.
- $forall P in CCS_seq . fi P atrans P' then e(P) wnu awtrans P'' and P' cr P''$
- $forall P in CCS_seq . fi e(P) atrans P' then P wnu awtrans P'' and P' cr P''$

The proof is done by induction on the height of the derivation tree, so we can rewrite it as follows:
- $forall P in CCS_seq . forall h in NN . fi P atrans P' "with a derivation tree of height" h then e(P) wnu awtrans P'' and P' cr P''$
- $forall P in CCS_seq . forall h in NN . fi e(P) atrans P' "with a derivation tree of height" h then P wnu awtrans P'' and P' cr P''$

=== First point
*base case h=1*

The only way a process can make a transition with derivation tree of height 1 is $ c1 $ and in this case also $ p1 $ and $P cr (e(P) wnu)$

*inductive case Const*

if $ c8 $ then by induction: $e(P) wnu atrans P'' wnu "and" P' cr (P'' wnu)$ 

$=> e(P) atrans P''$ so #v(1em) $ p2 $ and $P' cr (P'' wnu)$

*inductive case Hide*

if $ c6 $ then by induction: $e(P) wnu atrans P'' "and" P' cr P''$

and so $ p3 $ #v(1em)

$ 
e(P) wL wnu tilde e(P) wnu wL "and" e(P) wnu wL atrans P'' wL \
=> e(P) wL wnu atrans P''' "and" P''' tilde P'' wL \
P' cr P'' => (P' wL) cr (P'' wL) "*forse da giustificare bene, alla peggio si puo mettere ~~ invece che R*" \
(P' wL) cr (P'' wL) "and" P''' tilde (P'' wL) => P''' cr (P' wL)
$

*inductive case Red*

if $ c7 $ then by induction: $e(P) wnu atrans P'' wnu "and" P' cr (P'' wnu)$ 

$=> e(P) atrans P''$ so #v(1em) $ p4 $
#v(1em) $ P' cr (P'' wnu) => P'[f] cr (P'' [f] wnu) "*anche questa da giustificare*" $
