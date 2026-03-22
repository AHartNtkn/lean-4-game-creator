import Game.Metadata

World "Fintype"
Level 3

Title "Product Types"

Introduction "
# The Multiplication Principle for Types

If `α` has `m` elements and `β` has `n` elements, how many elements
does the product `α × β` have? Exactly `m * n` — every pair `(a, b)`
with `a : α` and `b : β` is a distinct element.

The theorem `Fintype.card_prod` captures this:

$$\\text{Fintype.card}\\;(\\alpha \\times \\beta) = \\text{Fintype.card}\\;\\alpha \\cdot \\text{Fintype.card}\\;\\beta$$

**Your task**: Prove the multiplication principle for `Fin n × Fin m`.

Notice the statement uses **variables** `n` and `m`, not fixed numbers.
You can't shortcut this with `rfl` — you must decompose with `card_prod`
and then evaluate with `card_fin`.
"

/-- The product Fin n × Fin m has n * m elements. -/
Statement (n m : ℕ) : Fintype.card (Fin n × Fin m) = n * m := by
  Hint "Use `rw [Fintype.card_prod]` to split the cardinality into
  `Fintype.card (Fin n) * Fintype.card (Fin m)`, then use
  `Fintype.card_fin` to evaluate each factor."
  Hint (hidden := true) "Try `rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]`."
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

Conclusion "
The multiplication principle for types:

$$|\\alpha \\times \\beta| = |\\alpha| \\cdot |\\beta|$$

This is the type-level version of the multiplication principle you know
from combinatorics. For example, `Fin 2 × Fin 3` has the 6 elements:
`(0,0), (0,1), (0,2), (1,0), (1,1), (1,2)`.

The proof pattern: `rw [card_prod, card_fin, card_fin]` — decompose
the product, then evaluate each factor.
"

/-- `Fintype.card_prod α β` states that
`Fintype.card (α × β) = Fintype.card α * Fintype.card β`.

The cardinality of a product type is the product of the cardinalities.

## Syntax
```
rw [Fintype.card_prod]    -- splits card (α × β) into card α * card β
```

## When to use it
When the goal or a hypothesis contains `Fintype.card (α × β)` and you
want to decompose it into a multiplication.

## Example
`Fintype.card (Fin 2 × Fin 3) = Fintype.card (Fin 2) * Fintype.card (Fin 3)`
-/
TheoremDoc Fintype.card_prod as "Fintype.card_prod" in "Fintype"

NewTheorem Fintype.card_prod

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
