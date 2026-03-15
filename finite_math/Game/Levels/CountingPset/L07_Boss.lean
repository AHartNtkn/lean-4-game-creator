import GameServer.Commands
import Mathlib

World "CountingPset"
Level 7

Title "Boss: Counting meets pigeonhole on a compound type"

Introduction
"
# Boss: Multi-step counting argument

Combine everything from this problem set into a single proof.

## The challenge

Consider a function from `Fin 3 × Fin 3` to `Fin 8`. The domain is a
product type with `3 × 3 = 9` elements. The codomain has `8` elements.
Since `9 > 8`, by pigeonhole there must be a collision: two distinct
inputs that map to the same output.

## What you need

1. `Fintype.exists_ne_map_eq_of_card_lt` to set up pigeonhole.
2. `Fintype.card_prod` to decompose the product type cardinality.
3. `Fintype.card_fin` to evaluate the cardinalities.
4. Arithmetic (`omega`) to close `8 < 3 * 3`.

This integrates the counting computation from Level 1 with the
pigeonhole application from Level 2.
"

/-- Any function from `Fin 3 × Fin 3` to `Fin 8` has a collision:
two distinct inputs that map to the same output. -/
Statement (f : Fin 3 × Fin 3 → Fin 8) :
    ∃ a b, a ≠ b ∧ f a = f b := by
  Hint (hidden := true) "Apply `Fintype.exists_ne_map_eq_of_card_lt`.
  The remaining goal is `Fintype.card (Fin 8) < Fintype.card (Fin 3 × Fin 3)`.
  Use `rw [Fintype.card_prod]` to decompose the product, then
  `rw [Fintype.card_fin, Fintype.card_fin]` to evaluate, and close
  with `omega`."
  apply Fintype.exists_ne_map_eq_of_card_lt
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  omega

Conclusion
"
Congratulations on completing the Counting and Pigeonhole problem set!

You proved that any function from a 9-element product type to an
8-element type must have a collision, by:

1. Applying `Fintype.exists_ne_map_eq_of_card_lt` to set up pigeonhole.
2. Using `Fintype.card_prod` to compute `|Fin 3 × Fin 3| = 3 × 3`.
3. Using `Fintype.card_fin` to evaluate each piece.
4. Closing the arithmetic: `8 < 9`.

## What you retrieved in this world

| Level | Skill | From world |
|-------|-------|-----------|
| L01 | Product cardinality with Bool (M13, M14) | W11, W12 |
| L02 | Pigeonhole collision (V16) | W12 |
| L03 | Reverse pigeonhole / no surjection (V15) | W12_ex |
| L04 | Nonemptiness from cardinality (V8, V9) | W12 |
| L05 | Transfer: pigeonhole in words (T5) | W12 |
| L06 | Transfer: exponential formula (T1) | W12, W12_ex |
| L07 | Integration | All |

## Transfer moment

In paper mathematics, this proof would read:

> *Let $f : \\{0,1,2\\} \\times \\{0,1,2\\} \\to \\{0,1,\\ldots,7\\}$.
> The domain has $3 \\times 3 = 9$ elements and the codomain has 8.
> Since $9 > 8$, by the pigeonhole principle there exist distinct
> pairs $(a_1, a_2) \\neq (b_1, b_2)$ with $f(a_1, a_2) = f(b_1, b_2)$.* $\\square$

The Lean proof is the same argument, mechanically verified.

## What comes next

The next world introduces `Finset.sum`: the big-sum operator that
lets you write and simplify expressions like $\\sum_{x \\in s} f(x)$.
"

TheoremTab "Fintype"
DisabledTactic trivial decide native_decide simp aesop simp_all
