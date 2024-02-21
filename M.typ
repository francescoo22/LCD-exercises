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

== Lemmas

0. $forall P in CCS_seq . P ended <=> e(P) ntrans P' and P' ended$ *si potrebbe formalizzare con HML*

1. $forall P in CCS_seq . forall L_1,L_2 in Act . P without L_1 without L_2 tilde P without L_2 without L_1$

2. $forall P in CCS_seq . P wnu [f] tilde P [f] wnu$ se f non fa cose con $nu$

== Equivalence

$ forall P in CCS_seq . P approx e(P) wnu $

let $ cr = {(P, Q) | P, Q in CCS_seq , Q approx e(P) wnu} union approx $

we need to prove that $cr$ is a weak bisimulation i.e.

- $forall P in CCS_seq . fi P atrans P' then e(P) wnu awtrans P'' wnu and P' cr (P'' wnu)$

- $forall P in CCS_seq . fi e(P) wnu atrans P'' wnu then P awtrans P' and P' cr (P'' wnu)$

The proof is done by induction on the height of the derivation tree, so we can rewrite it as follows:

- $forall P in CCS_seq . forall h in NN . fi P atrans P' "with tree of height" h then e(P) wnu awtrans P'' wnu and P' cr (P'' wnu)$

- $forall P in CCS_seq . forall h in NN . fi e(P) wnu atrans P'' wnu "with tree of height" h then P awtrans P' and P' cr (P'' wnu)$

=== First point
*base case h=1*

The only way a process can make a transition with derivation tree of height 1 is $ c1 $ and in this case also $ p1 $ and $P cr (e(P) wnu)$

*inductive case Const*

if $ c8 $ then by induction: $e(P) wnu atrans P'' wnu "and" P' cr (P'' wnu)$ 

$=> e(P) atrans P''$ so #v(1em) $ p2 $ and $P' cr (P'' wnu)$

*inductive case Hide*

if $ c6 $ then by induction: $e(P) wnu atrans P'' wnu "and" P' cr (P'' wnu)$

and so $ p3 $ #v(1em)

$ 
  e(P) wnu wL tilde^"lemma 1" e(P) wL wnu \
  =>^"bisim" e(P) wL wnu atrans P''' "and" (P'' wnu wL) tilde P'''
$

now we need to prove that $(P' wL) cr (P''')$

since $P' cr (P'' wnu)$ there are 2 cases:

1. case $P' approx (P'' wnu)$ : 
$ =>^("properties of " approx) (P' wL) approx (P'' wnu wL) =>^(("transitivity and" (P'' wnu wL) tilde P''')) P' wL approx P''' $ 

2. case $P'' wnu approx e(P') wnu$ : 
I have to show that $P''' approx (e(P' wL) wnu)$ so that $P''' cr (P' wL)$
$ 
  (P'' wnu wL) approx^("2 and properties of " approx) (e(P') wnu wL) tilde^"lemma 1" e(P') wL wnu = e(P' wL) wnu \
  (P'' wnu wL) tilde P''' "as showed before" \
  =>^("by transitivity") P''' approx (e(P' wL) wnu)
$

*inductive case Red*

if $ c7 $ then by induction: $e(P) wnu atrans P'' wnu "and" P' cr (P'' wnu)$

and so $ p4 $

$ 
  e(P) wnu [f] tilde^"lemma 2" e(P) [f] wnu \
  =>^"bisim" e(P) [f] wnu ->^(f(alpha)) P''' "and" (P'' wnu [f]) tilde P'''
$

To prove: $(P'[f]) cr P'''$

Since $P' cr (P'' wnu)$ there are 2 cases:

1. case $P' approx (P'' wnu)$ : 
$
  P' [f] approx^("case and properties of" approx) P'' wnu [f] tilde^"shown before" P'''
$

2. case $p'' wnu approx e(P') wnu$ :

I have to show that $P''' approx (e(P'[f]) wnu)$

$ P''' tilde^"shown before" P'' wnu [f] approx^("case and properties of" approx) e(P') wnu [f] tilde^"lemma 2" e(P')[f] wnu = e(P'[f]) wnu $