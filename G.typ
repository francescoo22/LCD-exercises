#import "common.typ": *

= Exercise G

Show that the encoding of the operator Even in the mu-calculus captures the property of interest:

$ hmlr(Even(phi)) = {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)} $

== Solution

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

=== Part 1

$ 
  S
  = {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)}\
  = {P | sat(P, phi) or P "can make a transition and " forall P_1 . P -> P_1 => forall "complete computation" P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)}\
  = {P | sat(P, phi) } union ({P | forall P ->^Act P' . P in S} sect {P | exists P ->^Act P' . P' in Proc})\
  = hmlr(phi) union (hmlr([Act] S) sect hmlr(ang(Act) T))\
  = hmlr(phi or ([Act] S and ang(Act) T))
  = f_phi (S)
  = S
$

$=> S$ is a fixed point of $f_phi$ , but $hmlr(Even(phi))$ is the lfp of $f_phi$
$=> hmlr(Even(phi)) subset.eq S = {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)}$

=== Part 2

Let $ S_n = {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i < n "s.t." sat(P_i, phi)} $
I want to prove that $forall n in NN . S_n subset.eq f_phi^n (emptyset)$

By induction on $n$:

*Base case $n=1$*

$ S_1 = {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i < 1 "s.t." sat(P_i, phi)} = {P | sat(P, phi)} \ subset.eq {P | sat(P, phi)} union hmlr([Act] emptyset and ang(Act)T) = hmlr(phi or ([Act] emptyset and ang(Act)T)) = f_phi (emptyset) $

*Inductive case $n => n+1$*

$ S_(n+1) = {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i < n+1 "s.t." sat(P_i, phi)} $

It is easy to see that 

$ 
S_(n+1) = {P | sat(P, phi) or P "can make a transition and " forall P_1 . P -> P_1 => forall "complete computation" P_1 -> "... " exists i < n "s.t." sat(P_i, phi)} \
= {P | sat(P, phi) } union ({P | forall P ->^Act P' . P in S_n} sect {P | exists P ->^Act P' . P' in Proc}) \
= hmlr(phi) union (hmlr([Act] S_n) sect hmlr(ang(Act) T)) \
$

By induction 
$ S_n subset.eq f_phi^n (emptyset) \
=> hmlr([Act] S_n) subset.eq hmlr([Act] f_phi^n (emptyset)) \
=> S_(n+1) = hmlr(phi) union (hmlr([Act] S_n) sect hmlr(ang(Act) T)) subset.eq hmlr(phi) union (hmlr([Act] f_phi^n (emptyset)) sect hmlr(ang(Act) T)) = f_phi^(n+1) (emptyset)
$

Since $2^Proc$ is a dcpo, By Kleene fixed-point theorem $ hmlr(Even(phi)) = fix(f_phi) = sup ({f_phi^n (emptyset) | n in NN}) $

and so 
$
forall n in NN . S_n subset.eq f_phi^n (emptyset) subset.eq fix(f_phi) = hmlr(Even(phi))\
=> {P | forall "complete computation" P = P_0 -> P_1 -> P_2 -> "... " exists i "s.t." sat(P_i, phi)} subset.eq hmlr(Even(phi))
$
