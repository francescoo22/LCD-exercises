#import "common.typ": *
#import "rules.typ": *

= Exercise M

Discuss an extension of CCS with an operator of sequential composition between processes $P; Q$. Provide an operational semantics and analyze the possibility of having an encoding in CCS of the defined operator.

*Solution*

== $CCS_seq$

$ P, Q ::= K | alpha . P | sum_(i in I) alpha . P_i | (P | Q) | P[f] | P without L | P;Q $

== Operational Semantics

// The following rules describe when a process has "finished" is work:

// $P$ has finished is work $equiv P ended$

*Rules:* 

// - for the moment $(P_1 + P_2);Q$ is not allowed, si puo fare anche solo con le guarded sum
// - think about a rule that defines when $P;Q ended$
// - idea per $0 approx e(0)$ è aggiungere alla weak bisim che $P ended P', P' ended, Q ended $
// - forse può aiutare dimostrare che $forall P . e(P) ended 0$
// - bisogna mettere la premessa che in CCSseq non ho canali $nu, nu', ...$ (si puo definire questa cosa per induzione strutturale)

#v(2em)

#grid(
  columns: (auto, auto, auto),
  column-gutter: 1fr,
  row-gutter: 2em,
  r1, r2, r3, r4, r5, r6, r7, r8
)

== Encoding

Let $e : CCS_seq times NN -> CCS$

The encoding of a $CCS_seq$ process $P$ is $e(P, 0) without {nu_0}$

Note: $forall i in NN . nu_i$ is a channel that does not appear in $P$

#list(
  tight: false,
  spacing: 2em,
  $e(0, i) = nu_i . 0$,
  $e(alpha . P, i) = alpha . e(P, i)$,
  $e(K, i) = K_e, space K_e def e(P, i) fi K def P$,
  $e(P | Q, i) = (e(P, i+1) | e(Q, i+1) | overline(nu_(i+1)) . overline(nu_(i+1)) . nu_i . 0) without {nu_(i+1)}$,
  $e(sum_(j in J, J != emptyset) alpha_j . P_j, i) = sum_(j in J, J != emptyset) alpha_j . e(P_j, i)$,
  $e(P[f], i) = e(P, i) [f]$,
  $e(P without L, i) = e(P, i) without L$,
  $e(P; Q, i) = (e(P, i+1) | overline(nu_(i+1)) . e(Q, i)) without {nu_(i+1)}$
)

== Equivalence

$ forall P in CCS_seq . forall i in NN . P approx e(P, i) wnu(i) $

Proprietà di $e$ da dimostrare

$ forall P in CCS_seq . forall i in NN . forall "trace" e(P, i) = P_0 -> P_1 -> ... P_(n-1) ->^alpha P_n space . space alpha = nu_i <-> P_n ended $

// Since $CCS subset.eq CCS_seq tab forall P in CCS_seq . e(P) in CCS_seq$

// We want to prove that $ forall P in CCS_seq . P approx e(P) wnu $

// By structural induction on $P$

// *case 0*

// we need to prove that $0 approx nu . 0 wnu$

// by definition, $0$ cannot make any transition and so it is vacuously true that $fi 0 ->^alpha P' "then" nu . 0 wnu =>^alpha Q' and P' approx Q'$

// It is also easy to see that $nu . 0 wnu$ cannot make any transition and so also the dual is valid.

// $
//   => fi cal(R) = emptyset then P cal(R) Q \ 
//   => 0 approx nu . 0 wnu
// $

// *case $alpha . P$*

// we need to prove that $alpha . P approx alpha . e(P) wnu$

// Since by construction, channels $nu, nu', ...$ can only be created by function $e$, we can say that $alpha != nu$

// The only transition that can be made by $alpha . P$ is by applying (Act) $ alpha . P ->^alpha P $
// Since $alpha != nu$ the only transition that can be made by $alpha . e(P) wnu$ is by applying (Res) $ alpha . e(P) wnu ->^alpha e(P) wnu $

// And by structural induction $P approx e(P) wnu$

// $
//   => cal(R) = (alpha . P, alpha . e(P) wnu) union approx \
//   => alpha . P approx alpha . e(P) wnu
// $

// *case K*

// we need to prove that $K approx K_e$ where $K def P "and" K_e def e(P)$

// it is easy to see that $K approx P$ and $K_e approx e(P)$

// by structural induction $P approx e(P)$

// and so by transitivity $K approx P, P approx e(P), e(P) approx K_e => K approx K_e$

// *case P|Q*

// we need to prove that $P|Q approx ((e(P)[nu'/nu] | e(Q)[nu'/nu] | overline(nu') . overline(nu') . nu . 0) without {nu'}) without {nu}$

// which is equivalent to prove that $P|Q approx (e(P)[nu'/nu] | e(Q)[nu'/nu] | overline(nu') . overline(nu') . nu . 0) without {nu', nu}$


// By structural induction:
// - $P approx e(P) wnu$
// - $Q approx e(Q) wnu$
