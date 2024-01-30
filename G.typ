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

TODO: saying that the set of all fixpoints is a lattice

$=> S$ is a fixed point of $f_phi$ , but $hmlr(Even(phi))$ is the lfp of $f_phi$
$=> hmlr(Even(phi)) subset.eq S = {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)}$