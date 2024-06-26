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

#include "encoding.typ"

#include "lemmas.typ"

== Equivalence

$ forall P in CCS_seq . P approx e(P) wnu $

let $ cr = {(P, Q wnu) | P, Q in CCS_seq , Q approx e(P)} $

we need to prove that $cr$ is a weak bisimulation i.e.

- $forall P in CCS_seq . fi P atrans P' then e(P) wnu awtrans P'' wnu and P' cr (P'' wnu)$

- $forall P in CCS_seq . fi e(P) wnu atrans P'' wnu then P awtrans P' and P' cr (P'' wnu)$

The proof is done by induction on the height of the derivation tree, so we can rewrite it as follows:

- $forall P in CCS_seq . forall h in NN . fi P atrans P' "with tree of height" h then e(P) wnu awtrans P'' wnu and P' cr (P'' wnu)$

- $forall P in CCS_seq . forall h in NN . fi e(P) wnu atrans P'' wnu "with tree of height" h then P awtrans P' and P' cr (P'' wnu)$

=== First point
*base case h=1*

The only way a process can make a transition with derivation tree of height 1 is $ c1 $ and in this case also $ p1 $ and $P cr (e(P) wnu)$ because $e(P) approx e(P)$

*inductive case Const*

if $ c8 $ 

$=>^"by induction" e(P) wnu atrans P'' wnu "and" P' cr (P'' wnu)$ 

$=> e(P) atrans P''$ so #v(1em) $ p2 $ and $P' cr (P'' wnu)$

*inductive case Hide*

if $ c6 $ 

$=>^"by induction" e(P) wnu awtrans P'' wnu "and" P' cr (P'' wnu)\
=>^"relation" P'' approx e(P')\
=>^"only rule"  e(P) awtrans P''$

$ p3 $

I have to prove that $P' wL cr P'' wL wnu$ i.e. $P'' wL approx e(P' wL)$

$ P'' wL approx^(P'' approx e(P')) e(P') wL = e(P' wL) $

*inductive case Red*

if $ c7 $ 

$=>^"by induction" e(P) wnu awtrans P'' wnu "and" P' cr (P'' wnu)\
=>^"only rule" e(P) awtrans P''$

and so $ p4 $

and $P''[f] approx^(P'' approx e(P')) e(P') [f] = e(P' [f]) => P'[f] cr P''[f] wnu$

*Inductive case Sum*

Sum case is trivial because if $ p5 $ also $ p6 $ 

and $P_j cr (e(P_j) wnu)$.

*Inductive case Par-1/Par-2/Par-3*

If $ c3 $ 

$=>^"by induction" e(P) wnu atrans P'' wnu "and" P' cr (P'' wnu)$

$=> e(P) atrans P''$

and so $ p7 $

#v(1em)

we need to show that $(P'|Q) cr (P''[nu'/nu] | e(Q)[nu'/nu] | overline(nu') . overline(nu') . nu . 0) wnup wnu$

which is equivalent to show that $(P''[nu'/nu] | e(Q)[nu'/nu] | overline(nu') . overline(nu') . nu . 0) wnup approx e(P'|Q)$

$ P' cr P'' wnu =>^(cr "definition") P'' approx e(P') \ =>^"bisim properties" (P''[nu'/nu] | e(Q)[nu'/nu] | overline(nu') . overline(nu') . nu . 0) wnup approx (e(P')[nu'/nu] | e(Q)[nu'/nu] | overline(nu') . overline(nu') . nu . 0) wnup = e(P'|Q) $

Par-2 and Par-3 are similar

*Inductive case Seq-L*

If $ r7 $

$=>^"by induction" e(P) wnu atrans P'' wnu "and" P' cr (P'' wnu)$

$=> e(P) atrans P''$

and so $ p8 $

#v(1em)

we need to show that $(P';Q) cr (P''[nu'/nu] | overline(v') . e(Q)) wnup wnu$

which is equivalent to show that $(P''[nu'/nu] | overline(v') . e(Q)) wnup approx e(P';Q)$

$ P' cr P'' wnu =>^(cr "definition") P'' approx e(P') \ =>^"bisim properties" (P''[nu'/nu] | overline(v') . e(Q)) wnup approx (e(P')[nu'/nu] | overline(v') . e(Q)) wnup = e(P';Q) $

*Inductive case Seq-R*

If $ r8 $

$P ended =>^"lemma 0" e(P) ->^(tau*) P_"temp" ntrans P' and P' ended$

$Q atrans Q'=>^"by induction" e(Q) wnu atrans Q'' wnu "and" Q' cr (Q'' wnu) => e(Q) atrans Q''$

and so $ p9 $

#v(2em)
$ p10 $
#v(2em)
$ p11 $
#v(2em)
Now I have to prove that $Q' cr (P' [nu'/nu] | Q'') wnup wnu$

Which is equivalent to prove that $(P' [nu'/nu] | Q'') wnup approx e(Q')$

$ P' ended =>^"End-Red" P'[nu'/nu] ended =>^"lemma 3" P'[nu'/nu] approx 0 \ => (P' [nu'/nu] | Q'') wnup approx (0 | Q'') wnup approx^(Q'' approx e(Q')) (0 | e(Q')) wnup approx^"lemma 4" 0 | e(Q') approx e(Q') $