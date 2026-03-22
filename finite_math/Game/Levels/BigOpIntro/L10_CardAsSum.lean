import Game.Metadata

World "BigOpIntro"
Level 10

Title "Cardinality as a Sum"

Introduction "
# The Bridge: Counting Is Summing

Here is a beautiful identity that connects everything you've learned
about cardinality with big operators:

$$|s| = \\sum_{x \\in s} 1$$

Counting the elements of a finset is the same as summing the constant
function 1 over that finset. Each element contributes 1 to the total,
and the total is the count.

In Lean, this is `Finset.card_eq_sum_ones`:
```
Finset.card_eq_sum_ones : s.card = ∑ x ∈ s, 1
```

This identity is the reason big operators *generalize* cardinality.
Cardinality answers \"how many?\" — summing answers \"how much?\" —
and `card = ∑ 1` shows that \"how many\" is the special case of
\"how much\" where every element contributes equally.

**Your task**: Prove that `s.card = ∑ x ∈ s, 1`.
"

/-- Cardinality equals the sum of the constant function 1. -/
Statement (s : Finset ℕ) : s.card = ∑ x ∈ s, 1 := by
  Hint "This is a direct application of `Finset.card_eq_sum_ones`.
  Use `rw` to rewrite the left side."
  Hint (hidden := true) "Try `rw [Finset.card_eq_sum_ones]`."
  rw [Finset.card_eq_sum_ones]

Conclusion "
You've proved the conceptual bridge between counting and summing:

$$|s| = \\sum_{x \\in s} 1$$

This identity explains why big operators are the natural generalization
of cardinality:
- **Cardinality**: each element contributes 1 → total = count
- **Weighted sum**: each element contributes f(x) → total = sum
- **Product**: each element contributes f(x) → total = product

Every cardinality argument you've seen so far can be restated as a
big-operator argument. The tools you learned in the Cardinality world
(`card_insert`, `card_singleton`, `card_empty`) are special cases of
`sum_insert`, `sum_singleton`, and `sum_empty` applied to the
constant function 1.
"

/-- `Finset.card_eq_sum_ones` states that `s.card = ∑ x ∈ s, 1`.

Cardinality is the sum of the constant function 1. This connects
the counting world (Phase 3) with the big-operator world (Phase 4).

## Syntax
```
exact Finset.card_eq_sum_ones
rw [Finset.card_eq_sum_ones]
```
-/
TheoremDoc Finset.card_eq_sum_ones as "Finset.card_eq_sum_ones" in "BigOp"

NewTheorem Finset.card_eq_sum_ones

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.sum_pair Finset.prod_pair
