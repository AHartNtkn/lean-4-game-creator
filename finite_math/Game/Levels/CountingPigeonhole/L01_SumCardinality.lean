import GameServer.Commands
import Mathlib

World "CountingPigeonhole"
Level 1

Title "Cardinality of sum types"

Introduction
"
# Counting and Pigeonhole

Welcome to the counting world! In the previous world you learned to compute
`Fintype.card` for `Fin n`, `Bool`, and product types. Now we extend this
to more type constructors, building toward the **pigeonhole principle**.

## Sum types

Given types `α` and `β`, the **sum type** `α ⊕ β` contains every element
of `α` (wrapped as `Sum.inl a`) and every element of `β` (wrapped as
`Sum.inr b`). The cardinality of a sum is the sum of the cardinalities:
```
Fintype.card_sum : Fintype.card (α ⊕ β) = Fintype.card α + Fintype.card β
```

This is the formal version of the **addition principle**: if set $A$ has
$m$ elements and set $B$ has $n$ elements, and $A$ and $B$ are disjoint,
then $A \\cup B$ has $m + n$ elements.

## Your task

Prove that `Fin 2 ⊕ Fin 3` has exactly 5 elements.

Use `Fintype.card_sum` to split the sum, then `Fintype.card_fin` to
evaluate each part.
"

/-- `Fin 2 ⊕ Fin 3` has exactly 5 elements. -/
Statement : Fintype.card (Fin 2 ⊕ Fin 3) = 5 := by
  Hint "Start with `rw [Fintype.card_sum]` to decompose the sum type cardinality
  into `Fintype.card (Fin 2) + Fintype.card (Fin 3)`."
  rw [Fintype.card_sum]
  Hint "Now the goal is `Fintype.card (Fin 2) + Fintype.card (Fin 3) = 5`.
  Rewrite both `Fintype.card (Fin _)` using `Fintype.card_fin`."
  Hint (hidden := true) "Use `rw [Fintype.card_fin, Fintype.card_fin]` to evaluate
  both cardinalities. The remaining goal `2 + 3 = 5` is handled by Lean."
  rw [Fintype.card_fin, Fintype.card_fin]

Conclusion
"
The addition principle in action:

1. `Fintype.card_sum` decomposed: `|\\text{Fin 2} \\oplus \\text{Fin 3}| =
   |\\text{Fin 2}| + |\\text{Fin 3}|`.
2. `Fintype.card_fin` evaluated: `2 + 3 = 5`.

## The addition principle

In ordinary counting, if you have two disjoint groups of objects, the total
count is the sum. The sum type `α ⊕ β` formalizes disjointness: every
element is tagged as either `inl` (from `α`) or `inr` (from `β`), so there
is no overlap.

**In plain language**: \"$\\{0, 1\\}$ and $\\{0, 1, 2\\}$ together give
$2 + 3 = 5$ elements (with no overlap, because each element remembers which
set it came from).\"
"

/-- `Fintype.card_sum` states that the cardinality of a sum type is the sum
of the cardinalities:
```
Fintype.card_sum : Fintype.card (α ⊕ β) = Fintype.card α + Fintype.card β
```

**When to use**: When computing the cardinality of `α ⊕ β` where both
`α` and `β` have `Fintype` instances. This is the formal addition
principle. -/
TheoremDoc Fintype.card_sum as "Fintype.card_sum" in "Fintype"

NewTheorem Fintype.card_sum
TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
