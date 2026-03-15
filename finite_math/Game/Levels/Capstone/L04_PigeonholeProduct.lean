import GameServer.Commands
import Mathlib

World "Capstone"
Level 4

Title "Pigeonhole on a product type"

Introduction
"
# Pigeonhole meets cardinality

The pigeonhole principle says: if the domain is larger than the
codomain, the function cannot be injective — there must be a collision.

## The setup

Consider a function `f : Fin 2 × Fin 3 → Fin 5`.

- The domain `Fin 2 × Fin 3` has `2 × 3 = 6` elements (by `Fintype.card_prod`).
- The codomain `Fin 5` has `5` elements (by `Fintype.card_fin`).
- Since `6 > 5`, pigeonhole guarantees a collision.

## The proof plan

1. **Apply pigeonhole**: `Fintype.exists_ne_map_eq_of_card_lt` to reduce
   the problem to proving `Fintype.card (Fin 5) < Fintype.card (Fin 2 × Fin 3)`.
2. **Compute cardinalities**: `card_prod` + `card_fin` to get `5 < 2 * 3`.
3. **Close arithmetic**: `omega`.

This integrates counting from the **FintypeClass** / **CountingPigeonhole**
worlds with the product-type infrastructure from **FinCompute** / **FintypeClass**.
"

/-- Any function from `Fin 2 × Fin 3` to `Fin 5` has a collision. -/
Statement (f : Fin 2 × Fin 3 → Fin 5) : ∃ a b, a ≠ b ∧ f a = f b := by
  Hint "Apply the collision form of pigeonhole:
  `apply Fintype.exists_ne_map_eq_of_card_lt`.

  This reduces the goal to proving that the codomain is smaller than
  the domain."
  Hint (hidden := true) "Try `apply Fintype.exists_ne_map_eq_of_card_lt`."
  apply Fintype.exists_ne_map_eq_of_card_lt
  Hint "The goal is `Fintype.card (Fin 5) < Fintype.card (Fin 2 × Fin 3)`.

  Decompose the product cardinality with `rw [Fintype.card_prod]`."
  Hint (hidden := true) "Try `rw [Fintype.card_prod]`."
  rw [Fintype.card_prod]
  Hint "Now evaluate each `Fintype.card (Fin _)` with `Fintype.card_fin`."
  Hint (hidden := true) "Try `rw [Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]`."
  rw [Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
  Hint "The goal is `5 < 2 * 3`. Close with `omega`."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion
"
You applied the pigeonhole principle to a product type, combining:

- **Pigeonhole** (`exists_ne_map_eq_of_card_lt`): reduces collision to a
  cardinality comparison.
- **Product cardinality** (`card_prod`): decomposes `|A × B| = |A| · |B|`.
- **Fin cardinality** (`card_fin`): evaluates `|Fin n| = n`.
- **Arithmetic** (`omega`): closes `5 < 6`.

## In ordinary mathematics

> *Since `Fin 2 × Fin 3` has $2 \\cdot 3 = 6$ elements and `Fin 5` has
> only $5$, any function between them must map two distinct inputs to the
> same output.* $\\square$

The Lean proof formalizes exactly this reasoning.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
