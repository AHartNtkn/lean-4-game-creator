import Game.Metadata

World "BigOpAlgebra"
Level 13

Title "Computing a Concrete Sum"

Introduction "
# Algebraic Tools Produce Numbers

So far, every level in this world has used abstract finsets and
functions. The algebraic tools rearranged sums without computing
them. But these same tools can **evaluate** sums to specific
numbers when you have enough information.

Here is a concrete scenario: you know the finset has 5 elements
and the sum of `f` over it equals 30. What is `∑ x ∈ s, (f x + f x + 1)`?

The split-simplify-substitute strategy from L03 gives the answer:
1. `sum_add_distrib` (twice) splits the summand into three pieces
2. `← card_eq_sum_ones` converts `∑ 1` to `s.card`
3. Hypothesis substitution plugs in the known values
4. The result is a number: `30 + 30 + 5 = 65`

**Your task**: Use the algebraic tools to evaluate this sum to 65.
"

/-- Use algebraic tools to evaluate a sum to a concrete number. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ)
    (hcard : s.card = 5) (hf : ∑ x ∈ s, f x = 30) :
    ∑ x ∈ s, (f x + f x + 1) = 65 := by
  Hint "The summand `f x + f x + 1` has the form `(f x + f x) + 1`.
  Use `rw [Finset.sum_add_distrib]` to split off the `+ 1`."
  rw [Finset.sum_add_distrib]
  Hint "The first part still has `f x + f x`. Apply
  `sum_add_distrib` again to split it."
  Hint (hidden := true) "Try `rw [Finset.sum_add_distrib]`."
  rw [Finset.sum_add_distrib]
  Hint "Now convert `∑ x ∈ s, 1` to `s.card` using
  `rw [← Finset.card_eq_sum_ones]`."
  Hint (hidden := true) "Try `rw [← Finset.card_eq_sum_ones]`."
  rw [← Finset.card_eq_sum_ones]
  Hint "Substitute the known values: `∑ f = 30` and `s.card = 5`."
  Hint (hidden := true) "Try `rw [hf, hcard]`."
  rw [hf, hcard]

Conclusion "
The algebraic tools just produced the number 65 from abstract
ingredients. Here is what happened step by step:

$$\\sum_{x \\in s}(f(x) + f(x) + 1) = \\sum f + \\sum f + \\sum 1 = 30 + 30 + 5 = 65$$

This is the split-simplify-substitute strategy working at full
power: algebraic tools reduce big-operator expressions to
arithmetic, and known values produce concrete answers.

**Preview**: The boss level uses the same summand `f x + f x + 1`
but over a disjoint union `s ∪ t` with additional structure. The
algebraic decomposition is the same — you just have more pieces
to manage.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
