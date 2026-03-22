import Game.Levels.FinsetInduction.L01_FirstContact
import Game.Levels.FinsetInduction.L02_BaseCase
import Game.Levels.FinsetInduction.L03_InductiveStep
import Game.Levels.FinsetInduction.L04_FullInduction
import Game.Levels.FinsetInduction.L05_AlgebraInStep
import Game.Levels.FinsetInduction.L06_MixedInduction
import Game.Levels.FinsetInduction.L07_ProductInduction
import Game.Levels.FinsetInduction.L08_ProductPractice
import Game.Levels.FinsetInduction.L09_Boss

World "FinsetInduction"
Title "Finset Induction"

Introduction "
# Finset Induction

You now know how to manipulate sums and products algebraically —
splitting summands, factoring, swapping order, peeling terms off
ranges. But all of those tools work by applying *existing* identities.

What if you need to prove a sum or product identity that isn't in
the library?

**Finset induction** is the answer. Just as you prove statements
about natural numbers by induction on $n$ (base case $0$, step
$n \\to n+1$), you can prove statements about finsets by induction
on $s$:

- **Base case**: prove the statement for $\\emptyset$
- **Inductive step**: given a finset $s$ and a fresh element
  $a \\notin s$, assume the statement holds for $s$ and prove it for
  $\\text{insert } a\\ s$

The inductive step always follows the same **collect-and-close**
pattern:
1. **Collect** — peel with `sum_insert ha` (or `prod_insert ha`),
   substitute the IH, peel cardinalities if needed
2. **Close** — finish the arithmetic with `ring` or `omega`

This world teaches the complete induction workflow for both sums
and products over arbitrary finsets.

**Prerequisites**: `sum_empty`, `sum_insert` from BigOpIntro,
`ring` from BigOpAlgebra, and `omega` from MeetFin.
"
