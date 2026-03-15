import GameServer.Commands
import Mathlib

World "FintypeClass"
Level 6

Title "Product types are Fintype"

Introduction
"
# `Fintype` propagation: products

One of the most powerful features of the `Fintype` class is that it
**propagates** through type constructors. If `α` and `β` are both
fintypes, then `α × β` is also a fintype, automatically.

The cardinality of a product type is the product of the cardinalities:
```
Fintype.card_prod : Fintype.card (α × β) = Fintype.card α * Fintype.card β
```

## Your task

Prove that `Fintype.card (Fin 2 × Fin 3) = 6`.

This requires a multi-step rewrite:
1. Use `Fintype.card_prod` to split the product cardinality.
2. Use `Fintype.card_fin` to evaluate each factor.
"

/-- `Fin 2 × Fin 3` has exactly 6 elements. -/
Statement : Fintype.card (Fin 2 × Fin 3) = 6 := by
  Hint "First, rewrite with `Fintype.card_prod` to express the product
  cardinality as a product of cardinalities.
  Try `rw [Fintype.card_prod]`."
  rw [Fintype.card_prod]
  Hint "The goal is now `Fintype.card (Fin 2) * Fintype.card (Fin 3) = 6`.
  You need to evaluate both `Fintype.card (Fin 2)` and `Fintype.card (Fin 3)`.
  Since `rw [Fintype.card_fin]` only rewrites one occurrence at a time,
  use `simp [Fintype.card_fin]` to handle both at once."
  Hint (hidden := true) "Use `simp [Fintype.card_fin]`. This rewrites all
  occurrences of `Fintype.card (Fin _)` and closes the arithmetic goal."
  simp [Fintype.card_fin]

Conclusion
"
The proof followed the multiplication principle:

1. `Fintype.card_prod` decomposed the product: `Fintype.card (Fin 2 × Fin 3) =
   Fintype.card (Fin 2) * Fintype.card (Fin 3)`.
2. `Fintype.card_fin` evaluated each factor: `2 * 3 = 6`.

## The multiplication principle

This is the formal version of the counting rule: if set $A$ has $m$
elements and set $B$ has $n$ elements, then $A \\times B$ has $m \\cdot n$
elements.

The `Fintype` class makes this automatic: Lean synthesizes the `Fintype`
instance for `Fin 2 × Fin 3` by combining the instances for `Fin 2` and
`Fin 3`. You never need to build the instance yourself --- Lean's type
class system handles it.

**In plain language**: \"The Cartesian product $\\{0,1\\} \\times \\{0,1,2\\}$
has $2 \\times 3 = 6$ elements.\"
"

TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
