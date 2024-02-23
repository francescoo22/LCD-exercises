#import "common.typ": *
#import "rules.typ": *

== Lemmas

0. $forall P in CCS_seq . P ended => e(P) ->^(tau*) P_"temp" ntrans P' and P' ended$

1. $forall P in CCS_seq . forall L_1,L_2 in Act . P without L_1 without L_2 tilde P without L_2 without L_1$

2. $forall P in CCS_seq . P wnu [f] tilde P [f] wnu$ se f non fa cose con $nu$

3. $forall P in CCS_seq . P ended => P approx 0$

4. $forall P in CCS_seq . e(P) approx e(P) wnup$

=== Lemma 0

$ forall P in CCS_seq . P ended => e(P) ->^(tau*) P_"temp" ntrans P' and P' ended $

By induction on the height of the derivation tree of $P ended$

*Base case End-Zero*

If $ r1 $

then $e(0) = nu . 0 ntrans 0$

*Inductive case End-Par*

If $ r2 $ then by induction $e(P) ->^(tau*) P_"temp" ntrans P' and P' ended$ and also $e(Q) ->^(tau*) Q_"temp" ntrans Q' and Q' ended$

So 
$ 
e(P|Q) = (e(P)[nu'/nu] | e(Q)[nu'/nu] | overline(nu') . overline(nu') . nu . 0)wnup \
->^(tau*) (P_"temp" [nu'/nu] | Q_"temp" [nu'/nu] | overline(nu') . overline(nu') . nu . 0) wnup \
ttrans (P'[nu'/nu] | Q_"temp" [nu'/nu] | overline(nu') . nu . 0) wnup \
ttrans (P'[nu'/nu] | Q'[nu'/nu] | nu . 0) wnup \
ntrans (P'[nu'/nu] | Q'[nu'/nu] | 0) wnup ended 
$

*Inductive case End-Seq*

If $ r6 $ then by induction $e(P) ->^(tau*) P_"temp" ntrans P' and P' ended$ and also $e(Q) ->^(tau*) Q_"temp" ntrans Q' and Q' ended$

So 
$
e(P; Q) = (e(P)[nu'/nu] | overline(nu') . e(Q)) wnup \
->^(tau*) (P_"temp" [nu'/nu] | overline(nu') . e(Q)) wnup \
ttrans (P' [nu'/nu] | e(Q)) wnup \
->^(tau*) (P' [nu'/nu] | Q_"temp") wnup \
ntrans (P' [nu'/nu] | Q') wnup ended
$