import GameServer.Commands
import Mathlib

World "CountingPigeonhole"
Level 10

Title "Boss: Pigeonhole on a compound type"

Introduction
"
# Boss: Counting meets pigeonhole

Time to combine the counting lemmas from this world with the pigeonhole
principle.

## The challenge

Consider a function from the sum type `Fin 2 ⊕ Fin 3` to `Fin 4`.
The domain has `2 + 3 = 5` elements (by `Fintype.card_sum`) and the
codomain has `4` elements. Since `5 > 4`, by pigeonhole there must be
a collision.

## What you need

1. `Fintype.exists_ne_map_eq_of_card_lt` to set up pigeonhole.
2. `Fintype.card_sum` to decompose the sum type cardinality.
3. `Fintype.card_fin` to evaluate the cardinalities.
4. Arithmetic (`omega`) to close `4 < 2 + 3`.

This integrates everything from the world: cardinality computation
(L01) and pigeonhole application (L08).
"

/-- Any function from `Fin 2 ⊕ Fin 3` to `Fin 4` has a collision. -/
Statement (f : Fin 2 ⊕ Fin 3 → Fin 4) :
    ∃ a b, a ≠ b ∧ f a = f b := by
  Hint "Start by applying the collision form of pigeonhole.
  Which lemma gives `∃ a b, a ≠ b ∧ f a = f b` from a cardinality
  comparison?"
  Hint (hidden := true) "Use `apply Fintype.exists_ne_map_eq_of_card_lt`."
  apply Fintype.exists_ne_map_eq_of_card_lt
  Hint "The goal is now
  `Fintype.card (Fin 4) < Fintype.card (Fin 2 ⊕ Fin 3)`.
  You need to compute `Fintype.card (Fin 2 ⊕ Fin 3)`. Which lemma
  decomposes a sum type cardinality?"
  Hint (hidden := true) "Use `rw [Fintype.card_sum]` to get
  `Fintype.card (Fin 4) < Fintype.card (Fin 2) + Fintype.card (Fin 3)`."
  rw [Fintype.card_sum]
  Hint "Now rewrite all the `Fintype.card (Fin _)` terms."
  Hint (hidden := true) "Use `rw [Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]`
  to get `4 < 2 + 3`. Then close with `omega`."
  rw [Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
  Hint (hidden := true) "The goal is `4 < 2 + 3`. Use `omega`."
  omega

Conclusion
"
Congratulations on completing the Counting and Pigeonhole world!

You proved that any function from a 5-element sum type to a 4-element
type must have a collision, by:

1. Applying `Fintype.exists_ne_map_eq_of_card_lt` to set up pigeonhole.
2. Using `Fintype.card_sum` to compute `|Fin 2 ⊕ Fin 3| = 2 + 3`.
3. Using `Fintype.card_fin` to evaluate each piece.
4. Closing the arithmetic with `omega`.

## What you learned in this world

| Concept | Level | Key item |
|---------|-------|----------|
| Sum type cardinality | L01 | `Fintype.card_sum` |
| Function type cardinality | L02 | `Fintype.card_fun` |
| Option type cardinality | L03 | `Fintype.card_option` |
| Nonempty witness extraction | L04 | `obtain` on `Nonempty` |
| Contradiction via card = 0 | L05 | `Finset.card_eq_zero` |
| Pigeonhole (non-injectivity) | L06--L07 | `Fintype.card_le_of_injective` |
| Pigeonhole (collision) | L08 | `exists_ne_map_eq_of_card_lt` |
| Natural-language application | L09 | Transfer |
| Integration | L10 | Counting + pigeonhole |

## Transfer moment

In paper mathematics, the pigeonhole principle says: if you put $n + 1$
objects into $n$ boxes, some box has at least two objects. The Lean version
says the corresponding function cannot be injective --- or equivalently,
that two distinct inputs map to the same output.

The formal proof is the same argument, made precise:
1. Count the domain and codomain.
2. Compare.
3. Conclude non-injectivity or exhibit a collision.

## What comes next

The next worlds build on these counting tools to explore concrete
examples, practice under reduced scaffolding, and extend the theory.
"

TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
