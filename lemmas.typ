#import "common.typ": *
#import "rules.typ": *

== Lemmas

0. $forall P in CCS_seq . P ended => e(P) ->^(tau*) P_"temp" ntrans P' and P' ended$

1. $fi forall P in CCS_seq . fi P atrans P' then e(P) wnu awtrans P'' wnu and P' cr (P'' wnu) \ then forall P in CCS_seq . fi P atrans P' "and" Q approx e(P) then Q wnu awtrans P'' wnu and P' cr (P'' wnu) "and dual"$

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

=== Lemma 1.1

$ 
fi forall P,Q in CCS_seq . fi P atrans P' then e(P) wnu awtrans P'' wnu and P' cr (P'' wnu) \ 
then forall P,Q in CCS_seq, P cr Q wnu . fi P atrans P' then Q wnu awtrans Q' wnu and P' cr (Q' wnu) 
$

*Proof:*

$e(P) wnu awtrans P'' wnu =>^"only rule" e(P) awtrans P'' =>^(Q approx e(P)) Q awtrans Q' and P'' approx Q' =>^"transitivity" Q' approx P' => P' cr Q' wnu$

=== Lemma 1.2

$
fi forall P,Q in CCS_seq . fi e(P) wnu atrans P'' wnu then P awtrans P' and P' cr (P'' wnu) \ 
then forall P,Q in CCS_seq, P cr Q wnu . fi Q wnu atrans Q' wnu then P awtrans P' and P' cr (Q' wnu)
$

*Proof:*

$Q wnu atrans Q' wnu =>^"only rule" Q atrans Q' =>^(Q approx e(P)) e(P) awtrans P'' and Q' approx P'' \
=>^"hide" e(P) wnu awtrans P'' wnu =>^"hypothesis" P awtrans P' and P' cr P'' wnu =>^"relation" P'' approx e(P') =>^"transitivity" Q' approx e(P')$