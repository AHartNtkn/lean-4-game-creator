import GameServer.Commands
import Mathlib

World "CountingPset"
Level 2

Title "Fresh pigeonhole application"

Introduction
"
# Pigeonhole in a new setting

Apply the pigeonhole principle to a function you have not seen before.

Given any function `f : Fin 7 → Fin 5`, prove that two distinct inputs
must collide (map to the same output).

The domain has 7 elements and the codomain has 5 elements. Since
`7 > 5`, by pigeonhole there must be a collision.

Recall:
```
Fintype.exists_ne_map_eq_of_card_lt (f : α → β) :
  Fintype.card β < Fintype.card α →
    ∃ x y, x ≠ y ∧ f x = f y
```
"

/-- Any function from `Fin 7` to `Fin 5` has a collision:
two distinct inputs mapping to the same output. -/
Statement (f : Fin 7 → Fin 5) : ∃ a b, a ≠ b ∧ f a = f b := by
  Hint (hidden := true) "Apply `Fintype.exists_ne_map_eq_of_card_lt`, then
  prove the cardinality condition with `rw [Fintype.card_fin, Fintype.card_fin]`
  and `omega`."
  apply Fintype.exists_ne_map_eq_of_card_lt
  rw [Fintype.card_fin, Fintype.card_fin]
  omega

Conclusion
"
You applied pigeonhole to `Fin 7 → Fin 5`: with 7 inputs and only 5
outputs, two inputs must share an output.

The proof pattern is the same as in the Counting and Pigeonhole world:
1. Apply `Fintype.exists_ne_map_eq_of_card_lt`.
2. Prove the cardinality condition: `5 < 7`.

**Retrieval check**: This level retrieved the pigeonhole collision move
(V16) on a fresh surface form (`Fin 7 → Fin 5` instead of
`Fin 5 → Fin 4` or `Fin 6 → Fin 5`).
"

DisabledTactic trivial decide native_decide simp aesop simp_all
