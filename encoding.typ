#import "common.typ": *

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