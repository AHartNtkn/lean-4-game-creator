import Game.Metadata

World "BigOpAlgebra"
Level 16

Title "The Cardinality-Summation Bridge"

Introduction "
# Cardinality IS Summation of 1s

In BigOpIntro, you proved `card_eq_sum_ones`:
```
Finset.card_eq_sum_ones : s.card = ∑ x ∈ s, 1
```

This says cardinality is a special case of summation — counting
elements is the same as summing the constant function 1.

This connection flows both ways:
- **Forward** (`card_eq_sum_ones`): `s.card` → `∑ x ∈ s, 1`
- **Backward** (`← card_eq_sum_ones`): `∑ x ∈ s, 1` → `s.card`

The backward direction is especially useful: when `sum_add_distrib`
produces a `∑ x ∈ s, 1` term, you can convert it back to `s.card`
using `rw [← Finset.card_eq_sum_ones]`.

**Your task**: Split `∑(f + 1)` into `∑f + ∑1`, then convert
`∑1` back to cardinality. This is exactly the pattern you'll
need in the boss level.
"

/-- Split a sum and convert the constant part to cardinality. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) :
    ∑ x ∈ s, (f x + 1) = (∑ x ∈ s, f x) + s.card := by
  Hint "Split the summand with `rw [Finset.sum_add_distrib]`."
  rw [Finset.sum_add_distrib]
  Hint "Now use `rw [← Finset.card_eq_sum_ones]` to convert
  `∑ x ∈ s, 1` back to `s.card`. The `←` arrow means rewrite
  right-to-left."
  Hint (hidden := true) "Try `rw [← Finset.card_eq_sum_ones]`."
  rw [← Finset.card_eq_sum_ones]

Conclusion "
The `sum_add_distrib` + `← card_eq_sum_ones` combination is a
standard pattern: whenever a summand has a `+ 1` (or `+ constant`)
component, split the sum and convert the constant part back.

**Why this matters**: The bridge between cardinality and summation
lets you move between counting problems and algebraic ones. When
you see `s.card` in a goal about sums, you can expand it to `∑ 1`.
When a sum computation produces `∑ 1`, you can collapse it to
`s.card`. This flexibility is central to many combinatorial proofs.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
