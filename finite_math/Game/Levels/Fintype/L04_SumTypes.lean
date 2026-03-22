import Game.Metadata

World "Fintype"
Level 4

Title "Sum Types"

Introduction "
# The Addition Principle for Types

The sum type `α ⊕ β` (typed `\\oplus`) contains elements that are
*either* from `α` or from `β`, but not both. If `α` has `m` elements
and `β` has `n` elements, then `α ⊕ β` has `m + n` elements.

The theorem `Fintype.card_sum` states:

$$\\text{Fintype.card}\\;(\\alpha \\oplus \\beta) = \\text{Fintype.card}\\;\\alpha + \\text{Fintype.card}\\;\\beta$$

**Contrast with products**: `×` multiplies, `⊕` adds.

**Your task**: Prove the addition principle for `Fin n ⊕ Fin m`.
"

/-- The sum type Fin n ⊕ Fin m has n + m elements. -/
Statement (n m : ℕ) : Fintype.card (Fin n ⊕ Fin m) = n + m := by
  Hint "Use `rw [Fintype.card_sum]` to split the cardinality into
  a sum, then `rw [Fintype.card_fin, Fintype.card_fin]` to evaluate."
  Hint (hidden := true) "Try `rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]`."
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

Conclusion "
The addition principle for types:

$$|\\alpha \\oplus \\beta| = |\\alpha| + |\\beta|$$

For example, the 5 elements of `Fin 2 ⊕ Fin 3` are:
`Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2`.

Each element is tagged with `inl` (left) or `inr` (right) to indicate
which component it came from. This is a *disjoint* union — even if
`α = β`, the elements are kept separate by their tags.

| Principle | Type | Cardinality |
|---|---|---|
| Multiplication | `α × β` | `card α * card β` |
| Addition | `α ⊕ β` | `card α + card β` |
"

/-- `Fintype.card_sum` states that
`Fintype.card (α ⊕ β) = Fintype.card α + Fintype.card β`.

The cardinality of a sum type is the sum of the cardinalities.

## Syntax
```
rw [Fintype.card_sum]    -- splits card (α ⊕ β) into card α + card β
```

## When to use it
When the goal or a hypothesis contains `Fintype.card (α ⊕ β)` and you
want to decompose it into an addition.

## Warning
`⊕` is a *disjoint* union. Even if `α = β`, the elements are kept
separate. Compare with `Finset.union` which deduplicates.
-/
TheoremDoc Fintype.card_sum as "Fintype.card_sum" in "Fintype"

NewTheorem Fintype.card_sum

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
