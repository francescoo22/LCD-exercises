#let Fix = "Fix"
#let fix = "fix"
#let Proc = "Proc"
#let Act = "Act"
#let Even = "Even"

#let hml(it) = $bracket.l.double it bracket.r.double$
#let hmlr(it) = $bracket.l.double it bracket.r.double_eta$
#let inangle(it) = $angle.l it angle.r$
#let sat(left, right) = $left tack.r.double right$