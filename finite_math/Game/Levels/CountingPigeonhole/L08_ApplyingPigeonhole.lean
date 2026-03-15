import GameServer.Commands
import Mathlib

World "CountingPigeonhole"
Level 8

Title "Applying pigeonhole: finding a collision"

Introduction
"
# From non-injectivity to collision

The pigeonhole principle says a function cannot be injective. But in
practice, we often want to find the actual **collision**: two distinct
inputs that map to the same output.

Mathlib provides a stronger form:
```
Fintype.exists_ne_map_eq_of_card_lt (f : α → β) :
  Fintype.card β < Fintype.card α →
    ∃ x y, x ≠ y ∧ f x = f y
```

This says: if the codomain is strictly smaller than the domain, then
there exist two distinct elements that `f` maps to the same value.

## Your task

Given any function `f : Fin 5 → Fin 4`, prove that two distinct inputs
collide.

The approach:
1. Apply `Fintype.exists_ne_map_eq_of_card_lt`.
2. Prove the cardinality condition: `Fintype.card (Fin 4) < Fintype.card (Fin 5)`.
"

/-- Any function from `Fin 5` to `Fin 4` has a collision:
two distinct inputs mapping to the same output. -/
Statement (f : Fin 5 → Fin 4) : ∃ a b, a ≠ b ∧ f a = f b := by
  Hint "Apply the mathlib pigeonhole lemma directly. Use
  `apply Fintype.exists_ne_map_eq_of_card_lt`.
  This reduces the goal to proving the cardinality condition."
  apply Fintype.exists_ne_map_eq_of_card_lt
  Hint "The goal is now `Fintype.card (Fin 4) < Fintype.card (Fin 5)`.
  Rewrite the cardinalities using `Fintype.card_fin` and close with
  arithmetic."
  Hint (hidden := true) "Use `rw [Fintype.card_fin, Fintype.card_fin]`
  to get `4 < 5`."
  rw [Fintype.card_fin, Fintype.card_fin]
  Hint (hidden := true) "The goal is `4 < 5`. Use `omega` to close it."
  omega

Conclusion
"
You used `Fintype.exists_ne_map_eq_of_card_lt` to extract an actual
collision from the pigeonhole principle.

## Two forms of pigeonhole

| Form | Statement | Use case |
|------|-----------|----------|
| Non-injectivity | `¬ Injective f` | When you only need to know injectivity fails |
| Collision | `∃ x y, x ≠ y ∧ f x = f y` | When you need the actual colliding pair |

The collision form is stronger: from `∃ x y, x ≠ y ∧ f x = f y` you can
derive `¬ Injective f`, but not vice versa (without further work).

## The API choice

Notice the input: `Fintype.card β < Fintype.card α` (strict inequality,
codomain < domain). This is equivalent to the non-injectivity condition
but is stated as a cardinality comparison that you prove with `rw` and
arithmetic.

**In plain language**: \"Among 5 objects placed in 4 slots, at least two
objects share a slot.\"
"

/-- `Fintype.exists_ne_map_eq_of_card_lt` is the collision form of the
pigeonhole principle:
```
Fintype.exists_ne_map_eq_of_card_lt (f : α → β) :
  Fintype.card β < Fintype.card α →
    ∃ x y, x ≠ y ∧ f x = f y
```

Given a function whose domain is strictly larger than its codomain,
this provides two distinct elements that map to the same value.

**When to use**: When you need to exhibit a concrete collision
(two inputs mapping to the same output), not just prove
non-injectivity. -/
TheoremDoc Fintype.exists_ne_map_eq_of_card_lt as "Fintype.exists_ne_map_eq_of_card_lt" in "Fintype"

NewTheorem Fintype.exists_ne_map_eq_of_card_lt
TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
