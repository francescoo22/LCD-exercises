#import "common.typ": *

= Exercise M

Discuss an extension of CCS with an operator of sequential composition between processes $P; Q$. Provide an operational semantics and analyze the possibility of having an encoding in CCS of the defined operator.

*Solution*

The operator $P;Q$ is interpreted as "$P$ will continue to move until it is possible, when $P$ is no longer able to make a move ($P ~ O$), $Q$ will start to move"

*Operational Semantics*

let $O = sum_(I in emptyset) P_i$

#align(center, box[ 
  #set text(10pt)
  #prooftree(
    axiom($P ->^alpha P'$),
    rule(label: "COMP-1", $P;Q ->^alpha P';Q$),
  )
])

#align(center, box[ 
  #set text(10pt)
  #prooftree(
    axiom($P ~ O$),
    rule(label: "COMP-2", $P;Q ->^tau Q$),
  )
])

#v(1em)
alternativa

#align(center, box[ 
  #set text(10pt)
  #prooftree(
    axiom($P ->^alpha P'$),
    axiom($P' tilde.not O$),
    rule(n:2, label: "COMP-1", $P;Q ->^alpha P';Q$),
  )
])

#align(center, box[ 
  #set text(10pt)
  #prooftree(
    axiom($P ->^alpha P'$),
    axiom($P' tilde O$),
    rule(n:2, label: "COMP-2", $P;Q ->^alpha Q$),
  )
])

*Encoding*

CCS-COMP processes

$ P, Q ::= K | alpha . P | sum_(i in I) P_i | (P | Q) | P[f] | P without L | P;Q $

let $comp(.) : "CCS-COMP" -> CCS$ defined as follows:

- $comp(K) = K_c, space K_c def comp(P) fi K def P$

- $comp(alpha . P) = alpha . comp(P)$

- $comp(sum_(i in I) P_i) = sum_(i in I) comp(P_i)$

- $comp(P | Q) = comp(P) | comp(Q)$

- $comp(P[f]) = comp(P) [f]$

- $comp(P without L) = comp(P) without L$

- $comp(P\;Q) = "comp"_(comp(Q))(comp(P))$

#v(2em)
where $compq(P) : CCS -> CCS$ with $Q in CCS$ is defined as follows:

- $compq(K) = K_Q, space K_Q def compq(P) fi K def P$

- $compq(alpha . P) = alpha . compq(P)$

- $
    "let" J subset.eq I = {i in I | P_i ~ O}\
    compq(sum_(i in I) P_i) = cases(
      Q fi I = J ("comprendo anche il caso " P = emptyset),
      sum_(j in I without J) compq(P_j) ("facendo così non mappo O + P a Q + P")
    )
  $

- $
    compq(P_1 | P_2) = cases(
      Q fi P_1 ~ O and P_2 ~ O,
      O | compq(P_2) fi P_1 ~ O and P_2 tilde.not O,
      compq(P_1) | O fi P_1 tilde.not O and P_2 ~ O,
      compq(P_1) | compq(P_2) fi P_1 tilde.not O and P_2 tilde.not O,
    )
  $

- $compq(P[f]) = ("comp"_(Q[g]) (P) [f]) [g^(-1)] space space space $ da definire formalmente cosa sia $g$, l'idea è che $g$ rinomina i canali che altrimenti verrebbero rinominati da $f$ con dei nomi "fresh" e poi con $g^(-1)$ riporto i nomi originali. Questo perché $compq(P[f]) != compq(P) [f]$

- $compq(P without L) = ("comp"_(Q[g]) (P) without L) [g^(-1)]$ stessa idea del punto precedente