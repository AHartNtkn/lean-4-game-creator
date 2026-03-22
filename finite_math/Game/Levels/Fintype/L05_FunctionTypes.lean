import Game.Metadata

World "Fintype"
Level 5

Title "Function Types"

Introduction "
# The Exponentiation Principle for Types

If `α` has `m` elements and `β` has `n` elements, how many functions
`f : α → β` exist? Each of the `m` inputs can be mapped to any of
the `n` outputs independently, giving `n^m` total functions.

The theorem `Fintype.card_fun` states:

$$\\text{Fintype.card}\\;(\\alpha \\to \\beta) = \\text{Fintype.card}\\;\\beta^{\\,\\text{Fintype.card}\\;\\alpha}$$

Notice: it's `card β ^ card α` — the *codomain* raised to the *domain*.

**Your task**: Prove the exponentiation principle for `Fin n → Fin m`.

After rewriting with `card_fun` and `card_fin`, the two sides become
equal.
"

/-- There are m ^ n functions from Fin n to Fin m. -/
Statement (n m : ℕ) : Fintype.card (Fin n → Fin m) = m ^ n := by
  Hint "The function type `Fin n → Fin m` is a composite type. Start by
  decomposing it with `Fintype.card_fun`, then evaluate each base type
  cardinality with `Fintype.card_fin`."
  Hint (hidden := true) "Try `rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]`."
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

Conclusion "
The exponentiation principle for types:

$$|\\alpha \\to \\beta| = |\\beta|^{|\\alpha|}$$

For example, the 9 functions `Fin 2 → Fin 3` correspond to the 9 ways
to assign each of the 2 inputs (0 and 1) to one of the 3 outputs (0, 1, or 2).

Notice there was no `omega` needed this time — after rewriting, both
sides were already equal. When you use concrete numbers (as in the
boss), you may need `omega` for the final arithmetic.

| Principle | Type | Cardinality |
|---|---|---|
| Multiplication | `α × β` | `card α * card β` |
| Addition | `α ⊕ β` | `card α + card β` |
| Exponentiation | `α → β` | `card β ^ card α` |
"

/-- `Fintype.card_fun` states that
`Fintype.card (α → β) = Fintype.card β ^ Fintype.card α`.

The cardinality of a function type is the codomain cardinality raised
to the domain cardinality.

## Syntax
```
rw [Fintype.card_fun]    -- splits card (α → β) into card β ^ card α
```

## When to use it
When the goal or a hypothesis contains `Fintype.card (α → β)` and you
want to decompose it into an exponentiation.

## Warning
The exponent is `card α` (the domain), not `card β`.
So `card (Fin 2 → Fin 3) = 3 ^ 2 = 9`, not `2 ^ 3 = 8`.
-/
TheoremDoc Fintype.card_fun as "Fintype.card_fun" in "Fintype"

NewTheorem Fintype.card_fun

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
