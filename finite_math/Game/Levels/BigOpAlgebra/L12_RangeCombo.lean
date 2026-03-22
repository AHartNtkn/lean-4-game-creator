import Game.Metadata

World "BigOpAlgebra"
Level 12

Title "Combining Range and Linearity"

Introduction "
# Combining sum_range_succ and sum_add_distrib

Now practice using two big-operator theorems together.

You know that `sum_range_succ` peels off the last term:
$$\\sum_{i=0}^{n} f(i) = \\sum_{i=0}^{n-1} f(i) + f(n)$$

And `sum_add_distrib` splits sums of sums:
$$\\sum(f + g) = \\sum f + \\sum g$$

**Your task**: Given the individual sums of `f` and `g` over
`range n`, compute the sum of `f + g` over `range (n + 1)`.
This requires peeling off the last term, then splitting the
remaining sum into two parts.
"

/-- Combine sum_range_succ and sum_add_distrib. -/
Statement (n : ℕ) (f g : ℕ → ℕ)
    (hf : ∑ i ∈ Finset.range n, f i = 30)
    (hg : ∑ i ∈ Finset.range n, g i = 20) :
    ∑ i ∈ Finset.range (n + 1), (f i + g i) = 50 + (f n + g n) := by
  Hint "Start by peeling off the last term with
  `rw [Finset.sum_range_succ]`."
  rw [Finset.sum_range_succ]
  Hint "Now the sum over `range n` has summand `f i + g i`.
  Split it with `rw [Finset.sum_add_distrib]`."
  Hint (hidden := true) "Try `rw [Finset.sum_add_distrib]`."
  rw [Finset.sum_add_distrib]
  Hint "Substitute the known sums."
  Hint (hidden := true) "Try `rw [hf, hg]`."
  rw [hf, hg]

Conclusion "
You combined two algebraic transformations:
1. `sum_range_succ` peeled off the last term
2. `sum_add_distrib` split the remaining sum by linearity

This is a preview of how proofs work in the SummationFormulas
world: peel off a term (by `sum_range_succ` or `sum_insert`),
transform the remaining sum algebraically, then close.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
