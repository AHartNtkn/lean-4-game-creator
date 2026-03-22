import Game.Metadata

World "FinsetInduction"
Level 2

Title "Practicing the Base Case"

Introduction "
# The Base Case Pattern

In a finset induction proof, the base case always involves the
empty set. For sum identities, this means:

1. Rewrite `\\sum x \\in \\emptyset, \\ldots` to `0` using `sum_empty`
2. Rewrite any other occurrences of `\\emptyset` (like `card \\emptyset = 0`)
3. Close the resulting arithmetic goal

The base case is usually the easy part, but getting fluent with it
matters — you'll write one in every finset induction proof.

**Your task**: This is the base case of the identity
$\\sum_{x \\in s} (f(x) + f(x)) = 2 \\cdot \\sum_{x \\in s} f(x)$.

Prove it for $s = \\emptyset$.
"

/-- The base case: sum over empty set. -/
Statement (f : ℕ → ℕ) :
    ∑ x ∈ (∅ : Finset ℕ), (f x + f x) = 2 * ∑ x ∈ (∅ : Finset ℕ), f x := by
  Hint "Both sides contain sums over `∅`. Use `sum_empty` to
  rewrite each one to `0`. You can do both in one step:
  `rw [Finset.sum_empty, Finset.sum_empty]`."
  Hint (hidden := true) "Try `rw [Finset.sum_empty, Finset.sum_empty]`."
  rw [Finset.sum_empty, Finset.sum_empty]
  Hint "The goal is now `0 = 2 * 0`. This is pure arithmetic.
  Use `ring` to close it."
  Hint (hidden := true) "Try `ring`."
  ring

Conclusion "
The base case pattern for sum identities:

1. `rw [Finset.sum_empty]` on each sum (or chain them)
2. Close the arithmetic (`ring`, `omega`, or `rfl`)

This will be the same in every induction proof. In the next
level, you'll practice the more interesting part: the inductive
step.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.sum_range_sub Finset.eq_sum_range_sub
