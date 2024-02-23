#import "common.typ": *

= Exercise G
#v(1em)

Show that the encoding of the operator Even in the mu-calculus captures the property of interest:

$ hmlr(Even(phi)) = { P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)} $

#v(1em)
*Solution*

As discussed during the lectures:
$
 Even(phi) = mu X . (phi or ([Act] X and ang(Act) T))\
 => hmlr(Even(phi)) = hmlr(mu X . (phi or ([Act] X and ang(Act) T))) = fix(f_phi)
$

where $f_phi (S) = hmlr(phi or ([Act] X and ang(Act) T))_[X->S] = hmlr(phi or ([Act] S and ang(Act) T))$

The proof can be divided in two parts:
+ $hmlr(Even(phi)) subset.eq {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)}$
+ $hmlr(Even(phi)) supset.eq {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)}$

In fact $1. and 2. => hmlr(Even(phi)) = { P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)}$

*Part 1*

$ 
  S
  = { P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)}\
  = {P | sat(P, phi) or P "can make a step and all the complete computations TODO"}\
  = { P | sat(P, phi) } union ({P | forall P ->^Act P' . P in S} sect {P | exists P ->^Act P' . P' in Proc})\
  = hmlr(phi) union (hmlr([Act] S) sect hmlr(ang(Act) T))\
  = hmlr(phi or ([Act] S and ang(Act) T))
  = f_phi (S)
  = S
$

$=> S$ is a fixed point of $f_phi$ , but $hmlr(Even(phi))$ is the lfp of $f_phi$
$=> hmlr(Even(phi)) subset.eq S = {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)}$

#v(1em)
*Part 2*

$
  hmlr(Even(phi)) = fix(f_phi)\
  = sect.big {x in 2^Proc | f_phi (x) subset.eq x}\
  = sect.big {x in 2^Proc | hmlr(phi or ([Act] X and ang(Act) T))_[X -> x]}\
  = sect.big {x in 2^Proc | {P | sat(P, phi)} union ([Act] x sect ang(Act) Proc) subset.eq x}
$

In order to prove that ${P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)} subset.eq hmlr(Even(phi))$

It is necessary to show that every $p in {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)}$

can be mapped to $hmlr(Even(phi)) = sect.big {X in 2^Proc | {P | sat(P, phi)} union ([Act] X sect ang(Act) Proc) subset.eq X}$

which is equivalent to show that given any $p in {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)}$
$forall X in 2^Proc | {P | sat(P, phi)} union ([Act] X sect ang(Act) Proc) subset.eq X$\
$p in X$

// Since $S = {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)}$ $= { P | sat(P, phi) } union ({P | forall P ->^Act P' . P in S} sect {P | exists P ->^Act P' . P' in Proc})$

// Two cases can be distinguished:
// + $p in { P | sat(P, phi) }$ ($p$ satisfies $phi$)

// + $p in  {P | forall P ->^Act P' . P in S} sect {P | exists P ->^Act P' . P' in Proc}$ ($p$ can move and for all the ways $p->p'$ it moves, $p' in S$)

// *Part 2 case 1*

// If
// $p in { P | sat(P, phi) }$

// Then given any
// $X in 2^Proc | {P | sat(P, phi)} union ([Act] X sect ang(Act) Proc) subset.eq X$ 

// It is also true that 
// ${P | sat(P, phi)} subset.eq X$

// $p in {P | sat(P, phi)} => p in X$

// *Part 2 case 2*

// - $p in [Act] S sect ang(Act) Proc$

*------------------------------------------*

let $S = {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)}$

given $p in S$

let $T = {P | P in "one of the complete computations of" p} sect {P | sat(P, phi)}$

A complete computation of $p$ can be written as follows: $p = P_i -> P_(i-1) -> P_(i-2) -> ... -> P_0 in T -> ...$

It can be shown that $forall i . P_i in X$

By induction on $i$:

*Case $i = 0$*

It is trivial to see that
${P | sat(P, phi)} subset.eq X => T subset.eq X => P_0 in X$

*Inductive Case*



// by contradiction: $exists X in 2^Proc | {P | sat(P, phi)} union ([Act] X sect ang(Act) Proc) subset.eq X and p in.not X$

