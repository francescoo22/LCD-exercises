#import "common.typ": *

= Exercise M

Discuss an extension of CCS with an operator of sequential composition between processes $P; Q$. Provide an operational semantics and analyze the possibility of having an encoding in CCS of the defined operator.

*Solution*

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
    axiom($Q ->^alpha Q'$),
    rule(label: "COMP-2", $O;Q ->^alpha Q$),
  )
])

oppure

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

let $comp(.) : "CCS-COMP" -> "CCS"$ defined as follows:

- $comp(K) = ?$

- $comp(alpha . P) = alpha . comp(P)$

- $comp(sum_(i in I) P_i) = sum_(i in I) comp(P_i)$

- $comp(P | Q) = comp(P) | comp(Q)$

- $comp(P[f]) = ?$

- $comp(P without L) = ?$

- $comp(P\;Q) = compq(P)$

where $compq(P) : "CCS" -> "CCS"$ with $Q in "CCS"$ is defined as follows: