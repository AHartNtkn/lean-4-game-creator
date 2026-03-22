import Game.Metadata

World "Cardinality"
Level 12

Title "Filtering Can't Increase Size"

Introduction "
# Connecting Filter and Cardinality

In FinsetOperations, you learned `Finset.filter` — selecting
elements that satisfy a predicate. In Level 11, you learned
`Finset.card_le_card` — subsets have smaller cardinality.

These two facts combine into a useful principle:

$$(s.\\text{filter}\\; p).\\text{card} \\leq s.\\text{card}$$

**Filtering can only shrink a set** (or keep it the same size).

The proof connects the two tools:
1. `Finset.filter_subset p s` gives `s.filter p ⊆ s`
2. `Finset.card_le_card` converts the subset to a cardinality bound

**Your task**: Prove that filtering never increases cardinality.
"

/-- Filtering a finset can only decrease (or preserve) its cardinality. -/
Statement (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (s.filter p).card ≤ s.card := by
  Hint "The filter is a subset of the original set:
  `Finset.filter_subset p s : s.filter p ⊆ s`.
  Apply `Finset.card_le_card` to convert this subset to a
  cardinality bound."
  Hint (hidden := true) "`exact Finset.card_le_card (Finset.filter_subset p s)`
  or use the two-step pattern:
  `have h := Finset.filter_subset p s`
  `exact Finset.card_le_card h`"
  exact Finset.card_le_card (Finset.filter_subset p s)

Conclusion "
You combined two tools from different worlds:
- `filter_subset` (FinsetOperations) — filtering produces a subset
- `card_le_card` (this world) — subsets have smaller cardinality

This is a common pattern in counting arguments: to bound the size
of a filtered set, you don't need to count its elements directly —
just observe that it's a subset of the original.

More generally, any operation that produces a subset
(`filter`, `inter`, `sdiff`) gives a cardinality upper bound
via `card_le_card`. This is the 'a part is never bigger than
the whole' principle applied to specific operations.
"

/-- `Finset.filter_subset p s` states that `s.filter p ⊆ s`.

Filtering a finset produces a subset of the original.

## Syntax
```
have h := Finset.filter_subset p s
```

## When to use it
When you need to establish that a filtered set is a subset of the
original, typically as a step toward a cardinality bound.
-/
TheoremDoc Finset.filter_subset as "Finset.filter_subset" in "Finset"

TheoremTab "Card"
NewTheorem Finset.filter_subset

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.card_filter_le
