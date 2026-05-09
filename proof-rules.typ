#import "@preview/curryst:0.5.0": rule, prooftree

#set page(width: auto, height: auto, margin: 0.6em)
#set text(font: "New Computer Modern", size: 11pt)

#let R(name: none, conclusion, ..premises) = {
  prooftree(rule(name: name, conclusion, ..premises))
}

#let seq = $arrow.r.double$

#grid(
  columns: 2,
  column-gutter: 4em,
  row-gutter: 2em,
  align: center + horizon,

  R(name: $"Ax"$,
    $A, Gamma seq A, Delta$),
  R(name: $bot L$,
    $bot, Gamma seq Delta$),

  R(name: $not L$,
    $not F, Gamma seq Delta$,
    $Gamma seq F, Delta$),
  R(name: $not R$,
    $Gamma seq not F, Delta$,
    $F, Gamma seq Delta$),

  R(name: $and L$,
    $F and G, Gamma seq Delta$,
    $F, G, Gamma seq Delta$),
  R(name: $and R$,
    $Gamma seq F and G, Delta$,
    $Gamma seq F, Delta$,
    $Gamma seq G, Delta$),

  R(name: $or L$,
    $F or G, Gamma seq Delta$,
    $F, Gamma seq Delta$,
    $G, Gamma seq Delta$),
  R(name: $or R$,
    $Gamma seq F or G, Delta$,
    $Gamma seq F, G, Delta$),

  R(name: $arrow.r L$,
    $F arrow.r G, Gamma seq Delta$,
    $Gamma seq F, Delta$,
    $G, Gamma seq Delta$),
  R(name: $arrow.r R$,
    $Gamma seq F arrow.r G, Delta$,
    $F, Gamma seq G, Delta$),

  R(name: $forall L$,
    $forall x. F, Gamma seq Delta$,
    $F[t slash x], forall x. F, Gamma seq Delta$),
  R(name: $forall R "(*)"$,
    $Gamma seq forall x. F, Delta$,
    $Gamma seq F[y slash x], Delta$),

  R(name: $exists L "(*)"$,
    $exists x. F, Gamma seq Delta$,
    $F[y slash x], Gamma seq Delta$),
  R(name: $exists R$,
    $Gamma seq exists x. F, Delta$,
    $Gamma seq F[t slash x], exists x. F, Delta$),
)

#v(0.5em)
#align(center)[
  #text(size: 9pt)[(\*) #h(0.3em) $y$ not free in the conclusion of the rule.]
]
