#import "typst-prooftree/prooftree.typ": *

#let Fix = "Fix"
#let fix = "fix"
#let Proc = "Proc"
#let Act = "Act"
#let Even = "Even"
#let compq = $"comp"_Q$

#let hml(it) = $bracket.l.double it bracket.r.double$
#let hmlr(it) = $bracket.l.double it bracket.r.double_eta$
#let comp(it) = $bracket.l.double it bracket.r.double_"comp"$
#let ang(it) = $angle.l it angle.r$
#let sat(left, right) = $left tack.r.double right$