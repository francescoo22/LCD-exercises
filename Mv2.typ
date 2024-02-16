#import "common.typ": *
#import "rules.typ": *

= Exercise M

Discuss an extension of CCS with an operator of sequential composition between processes $P; Q$. Provide an operational semantics and analyze the possibility of having an encoding in CCS of the defined operator.

*Solution*

The operator $P;Q$ is interpreted as "$P$ will continue to move until it is possible, when $P$ is no longer able to make a move ($P ~ O$), $Q$ will start to move"

== $CCS_comp$

$ P, Q ::= K | alpha . P | sum_(i in I) P_i | (P | Q) | P[f] | P without L | P;Q $

== Operational Semantics

The following rules describe when a process has "finished" is work:

$P$ has finished is work $equiv P ->^nu$

*Rules:* 

- for the moment $(P_1 + P_2);Q$ is not allowed, si puo fare anche solo con le guarded sum
- think about a rule that defines when $P;Q ended$
- idea per $0 approx e(0)$ è aggiungere alla weak bisim che $P ended P', P' ended, Q ended $
- forse può aiutare dimostrare che $forall P . e(P) ended 0$
- bisogna mettere la premessa che in CCScomp non ho canali $nu, nu', ...$ (si puo definire questa cosa per induzione strutturale)

#v(2em)

#grid(
  columns: (auto, auto, auto),
  column-gutter: 1fr,
  row-gutter: 2em,
  r1, r2, r3, r4, r5, r7, // r6, r8
)

== Encoding

Let $e : CCS_comp -> CCS$ encoding function from $CCS_comp$ to $CCS$ defined as follows:

#list(
  tight: false,
  spacing: 2em,
  $e(0) = nu . 0$,
  $e(alpha . P) = alpha . e(P)$,
  $e(K) = K_e, space K_e def e(P) fi K def P$,
  $e(P | Q) = (e(P)[nu'/nu] | e(Q)[nu'/nu] | overline(nu') . overline(nu') . nu . 0) without {nu'}$,
  $e(sum_(i in I) P_i) = sum_(i in I) e(P_i)$,
  $e(P[f]) = e(P) [f]$,
  $e(P without L) = e(P) without L$,
  $e(P; Q) = (e(P) | overline(nu) . e(Q)) wnu "forse togliere il canale nascosto"$
)

The final encoding of a process $P$ is $e(P) wnu$

== Equivalence

Since $CCS subset.eq CCS_seq tab forall P in CCS_seq . e(P) in CCS_seq$

We want to prove that $ forall P in CCS_seq . P approx e(P) wnu $

By structural induction on $P$

*case 0*

we need to prove that $0 approx nu . 0 wnu$

by definition, $0$ cannot make any transition and so it is vacuously true that $fi 0 ->^alpha P' "then" nu . 0 wnu =>^alpha Q' and P' approx Q'$

It is also easy to see that $nu . 0 wnu$ cannot make any transition and so also the dual is valid.

$
  => fi cal(R) = emptyset then P cal(R) Q \ 
  => 0 approx nu . 0 wnu
$

*case $alpha . P$*

we need to prove that $alpha . P approx alpha . e(P) wnu$

Since by construction, channels $nu, nu', ...$ can only be created by function $e$, we can say that $alpha != nu$

The only transition that can be made by $alpha . P$ is by applying (Act) $ alpha . P ->^alpha P $
Since $alpha != nu$ the only transition that can be made by $alpha . e(P) wnu$ is by applying (Res) $ alpha . e(P) wnu ->^alpha e(P) wnu $

And by structural induction $P approx e(P) wnu$

$
  => cal(R) = (alpha . P, alpha . e(P) wnu) union approx \
  => alpha . P approx alpha . e(P) wnu
$

*case K*

we need to prove that $K approx K_e$ where $K def P "and" K_e def e(P)$

it is easy to see that $K approx P$ and $K_e approx e(P)$

by structural induction $P approx e(P)$

and so by transitivity $K approx P, P approx e(P), e(P) approx K_e => K approx K_e$

*case P|Q*

we need to prove that $P|Q approx ((e(P)[nu'/nu] | e(Q)[nu'/nu] | overline(nu') . overline(nu') . nu . 0) without {nu'}) without {nu}$

which is equivalent to prove that $P|Q approx (e(P)[nu'/nu] | e(Q)[nu'/nu] | overline(nu') . overline(nu') . nu . 0) without {nu', nu}$


By structural induction:
- $P approx e(P) wnu$
- $Q approx e(Q) wnu$
