import GameServer.Commands
import Mathlib

World "CountingPset"
Level 1

Title "Count a new compound type"

Introduction
"
# Counting and Pigeonhole: Problem Set

Welcome to the problem set for counting and pigeonhole. In this world
you will retrieve skills from the Counting and Pigeonhole world and
the Counting Functions world under **reduced scaffolding**: fewer hints,
fresh surface forms, and no new theorems.

## Level 1: Counting a product type with Bool

Compute the cardinality of `Fin 4 × Bool`. This is a product type you
have not seen before.

Recall:
- `Fintype.card_prod` decomposes a product cardinality.
- `Fintype.card_fin` evaluates `Fintype.card (Fin n)`.
- `Fintype.card_bool` evaluates `Fintype.card Bool`.
"

/-- `Fin 4 × Bool` has exactly 8 elements. -/
Statement : Fintype.card (Fin 4 × Bool) = 8 := by
  Hint (hidden := true) "Use `rw [Fintype.card_prod]` to split the product,
  then `rw [Fintype.card_fin, Fintype.card_bool]` to evaluate."
  rw [Fintype.card_prod]
  rw [Fintype.card_fin, Fintype.card_bool]

Conclusion
"
You computed `Fintype.card (Fin 4 × Bool) = 4 * 2 = 8`.

The proof used the multiplication principle: a pair from a 4-element set
and a 2-element set gives `4 × 2 = 8` possible pairs.

**Retrieval check**: This level retrieved the product cardinality
computation (M13, M14) on a fresh surface form (`Fin 4 × Bool` instead
of `Fin 2 × Fin 3`).
"

DisabledTactic trivial decide native_decide simp aesop simp_all
