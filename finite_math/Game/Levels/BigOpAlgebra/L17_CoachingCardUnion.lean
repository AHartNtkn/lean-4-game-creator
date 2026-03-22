import Game.Metadata

World "BigOpAlgebra"
Level 17

Title "Coaching: Card-Sum Bridge Meets Union Splitting"

Introduction "
# Combining ← card_eq_sum_ones with sum_union

Before the boss, let's practice combining two skills that you've
each seen once:

- **← card_eq_sum_ones** (from L16): converts `∑ x ∈ s, 1` back
  to `s.card`
- **sum_union** (from L06): splits `∑ x ∈ s ∪ t, f x` into
  `∑ x ∈ s, f x + ∑ x ∈ t, f x` when `s` and `t` are disjoint

This level combines all four of the big-operator moves you'll need
in the boss: `sum_add_distrib` to split the summand,
`← card_eq_sum_ones` to convert the constant sum to cardinality,
`sum_union` to split by the disjoint union, and hypothesis
substitution to plug in known values.

**Your task**: Given the sum of `f` over `s` and a disjoint
union `s ∪ t`, prove the identity.
"

/-- Practice combining sum_add_distrib, ← card_eq_sum_ones, and sum_union. -/
Statement (s t : Finset ℕ) (f : ℕ → ℕ) (h : Disjoint s t)
    (hs : ∑ x ∈ s, f x = 10) :
    ∑ x ∈ s ∪ t, (f x + 1) = 10 + (∑ x ∈ t, f x) + (s ∪ t).card := by
  Hint "Start by splitting the summand `f x + 1` into two sums
  using `rw [Finset.sum_add_distrib]`."
  rw [Finset.sum_add_distrib]
  Hint "Now use `rw [← Finset.card_eq_sum_ones]` to convert
  `∑ x ∈ s ∪ t, 1` back to `(s ∪ t).card`."
  Hint (hidden := true) "Try `rw [← Finset.card_eq_sum_ones]`."
  rw [← Finset.card_eq_sum_ones]
  Hint "Split the union sum using `rw [Finset.sum_union h]` with
  the disjointness hypothesis."
  Hint (hidden := true) "Try `rw [Finset.sum_union h]`."
  rw [Finset.sum_union h]
  Hint "Substitute the known sum value with `rw [hs]`."
  Hint (hidden := true) "Try `rw [hs]`."
  rw [hs]

Conclusion "
You just executed the four-step pattern that the boss will require:

1. `sum_add_distrib` — split the summand into parts
2. `← card_eq_sum_ones` — convert `∑ 1` to cardinality
3. `sum_union h` — split a union sum using disjointness
4. Hypothesis substitution — plug in known values

The boss adds two more ingredients: `ring` to close the final
algebra, and you may need to apply `sum_add_distrib` **more than
once** if the summand has multiple additive components (e.g.,
`f x + g x + 1` requires splitting twice).
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
