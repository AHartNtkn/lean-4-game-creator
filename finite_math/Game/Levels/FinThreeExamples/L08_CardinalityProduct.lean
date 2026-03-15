import GameServer.Commands
import Mathlib

World "FinThreeExamples"
Level 8

Title "Counting elements of Fin 3 x Fin 3"

Introduction
"
# The Multiplication Principle for `Fin 3`

You have been constructing elements of `Fin 3 × Fin 3` and reasoning
about functions on `Fin 3`. Now let's count: how many elements does
`Fin 3 × Fin 3` have?

`Fintype.card (Fin 3 × Fin 3)` computes the cardinality of the product
type. The answer is `3 × 3 = 9`.

## Your task

Prove `Fintype.card (Fin 3 × Fin 3) = 9`.

This requires a multi-step proof. The key lemma is
`Fintype.card_prod`, which says:
```
Fintype.card (α × β) = Fintype.card α * Fintype.card β
```

After rewriting with `Fintype.card_prod`, the goal becomes
`Fintype.card (Fin 3) * Fintype.card (Fin 3) = 9`.

Then use `Fintype.card_fin` (which says `Fintype.card (Fin n) = n`)
to simplify further. The `rw` tactic can handle both rewrites.
"

/-- `Fin 3 × Fin 3` has exactly 9 elements. -/
Statement : Fintype.card (Fin 3 × Fin 3) = 9 := by
  Hint "The cardinality of a product type equals the product of the cardinalities.
  Rewrite using `Fintype.card_prod`: try `rw [Fintype.card_prod]`."
  rw [Fintype.card_prod]
  Hint "The goal is now `Fintype.card (Fin 3) * Fintype.card (Fin 3) = 9`.
  Use `Fintype.card_fin` to replace `Fintype.card (Fin 3)` with `3`.
  Try `rw [Fintype.card_fin]`."
  Hint (hidden := true) "After `rw [Fintype.card_fin]`, the goal becomes `3 * 3 = 9`,
  which is a concrete arithmetic fact."
  rw [Fintype.card_fin]

/-- `Fintype.card_prod` states that `Fintype.card (α × β) = Fintype.card α * Fintype.card β`.
The cardinality of a product type is the product of the cardinalities.

**When to use**: When you need to count the elements of a product type.

**Example**: `Fintype.card (Fin 3 × Fin 2) = 3 * 2 = 6`. -/
TheoremDoc Fintype.card_prod as "Fintype.card_prod" in "Fintype"

/-- `Fintype.card_fin` states that `Fintype.card (Fin n) = n`.
The type `Fin n` has exactly `n` elements.

**When to use**: When simplifying cardinality expressions involving `Fin n`. -/
TheoremDoc Fintype.card_fin as "Fintype.card_fin" in "Fintype"

NewTheorem Fintype.card_prod Fintype.card_fin
TheoremTab "Fintype"

DisabledTactic trivial decide native_decide simp aesop simp_all norm_num

Conclusion
"
`Fin 3 × Fin 3` has exactly 9 elements. The proof decomposed into two steps:

1. `Fintype.card_prod`: the cardinality of a product equals the product
   of the cardinalities
2. `Fintype.card_fin`: `Fin n` has `n` elements

So `Fintype.card (Fin 3 × Fin 3) = Fintype.card (Fin 3) * Fintype.card (Fin 3) = 3 * 3 = 9`.

**The multiplication principle**: If set $A$ has $m$ elements and set $B$
has $n$ elements, then $A \\times B$ has $m \\cdot n$ elements. This is one
of the most fundamental counting principles, and you have just seen its
formal statement in Lean.

**Preview**: In later worlds, you will use `Fintype.card` to count more
complex finite types: sum types (`α ⊕ β`), function types (`α → β`),
and subtypes (`{x : α // P x}`). Each has its own cardinality formula.

**In plain language**: \"The Cartesian product $\\{0,1,2\\} \\times \\{0,1,2\\}$
has $3 \\times 3 = 9$ elements.\"
"
