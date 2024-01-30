#import "common.typ": *

*Monotone function*

$f : 2^A -> 2^A$ monotone if $" "forall x,y in 2^A . x subset.eq y -> f(x) subset.eq f(y)$

*Knaster-Tarski fixed-point*

Given $f : 2^A -> 2^A$ monotone, then $f$ has
- greatest fixed point $Fix(f) = union.big {x in 2^A | x subset.eq f(x)}$
- least fixed point $fix(f) = sect.big {x in 2^A | x supset.eq f(x)}$

If $A$ is finite, $f : 2^A -> 2^A$ monotone
- $Fix(f) = f^k (A)$ for some $k in NN$
- $fix(f) = f^h (emptyset)$ for some $h in NN$

*Hennessy-Milner Logics*

$ phi, psi ::= T | F | phi and psi | phi or psi | ang(a) phi | [a] phi $

- $hml(" ") : "HML" -> 2^Proc$
- $hml(phi) subset.eq Proc$
- $P tack.r.double phi$ stands for $P in hml(phi)$

*Definitions*

- $hml(T) = Proc$
- $hml(F) = emptyset$
- $hml(phi and psi) = hml(phi) sect hml(psi)$
- $hml(phi or psi) = hml(phi) union hml(psi)$
- $hml(ang(a)phi) = ang(a) hml(phi) "   for " X subset.eq Proc ang(a) X = {P | exists P ->^a P' and P' in X}$
- $hml([a]phi) = [a] hml(phi) "   for " X subset.eq Proc [a] X = {P | forall P ->^a P' and P' in X}$

*Image finiteness*

$P$ is image-finite if ${P' | P ->^a P'}$ is finite $forall a in Act$

*Hennessy-Milner Theorem*

Let $P, Q$ image-finite $ P ~ Q <-> (forall phi in "HML" sat(P, phi) <-> sat(Q, phi)) $

*HML with recursion*

- $"Inv"(phi) = nu X . (phi and [Act] X)$

- $"Pos"(phi) = mu Y . (phi or ang(Act) Y)$

- $Even(phi) = mu X . (phi or ([Act] X and ang(Act) T))$

*$mu$-calculus*

$ phi, psi ::= T | F | phi and psi | phi or psi | ang(a) phi | [a] phi | X | nu X . phi | mu X . phi $

where:
- $X : "Var"$
- $eta : "Var" -> 2^Proc$
- $hmlr(phi) subset.eq Proc$

- $hmlr(T) = Proc$
- $hmlr(F) = emptyset$
- $hmlr(phi and psi) = hmlr(phi) sect hmlr(psi)$
- $hmlr(phi or psi) = hmlr(phi) union hmlr(psi)$
- $hmlr(ang(a)phi) = ang(a) hmlr(phi)$
- $hmlr([a]phi) = [a] hmlr(phi)$
- $hmlr(X) = eta(X)$
- $hmlr(nu X . phi) = Fix(f_phi), " "S =^max hmlr(phi)_[x->S] = f_phi (S)$
- $hmlr(mu X . phi) = fix(f_phi)$