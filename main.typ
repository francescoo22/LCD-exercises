#import "@local/unipd-doc:0.0.1": *

#show: unipd-doc(
  title: "Internship Project Proposal",
  subtitle: "Using Viper to formally verify\nKotlin code",
  author: "Protopapa Francesco",
  date: "2023/01/26",
)

#pagebreak()
#show link: it => {
  set text(fill: blue)
  underline(it)
}

// Add background to monospace text
#show raw.where(block: false): box.with(
  fill: luma(220),
  inset: (x: 3pt, y: 0pt),
  outset: (y: 3pt),
  radius: 4pt,
)
#show raw.where(block: true): block.with(
  fill: luma(220),
  inset: 10pt,
  radius: 5pt,
)

#include "G.typ"
#pagebreak()
#include "M.typ"