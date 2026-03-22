import Game.Metadata

World "BigOpIntro"
Level 9

Title "Base Case Contrast"

Introduction "
# Additive vs. Multiplicative Base Cases

Quick review: what are the empty sum and empty product?

- `∑ x ∈ ∅, f x = ?` — the additive identity: **0**
- `∏ x ∈ ∅, f x = ?` — the multiplicative identity: **1**

Confusing these is a common mistake. This level forces you to
use both in the same proof, so the distinction sticks.

**Your task**: You know that `s` is empty. The expression is a sum
plus a product over `s`. Substitute `s`, simplify both base cases,
and compute the result.
"

/-- The empty sum is 0 and the empty product is 1. -/
Statement (f : ℕ → ℕ) (s : Finset ℕ) (hs : s = ∅) :
    (∑ x ∈ s, f x) + (∏ x ∈ s, f x) = 1 := by
  Hint "First substitute `s` with its value using `rw [hs]`."
  rw [hs]
  Hint "Now simplify the empty sum with `rw [Finset.sum_empty]`.
  Then simplify the empty product."
  rw [Finset.sum_empty]
  Hint "The sum is gone (replaced by 0). Now simplify the empty
  product with `rw [Finset.prod_empty]`."
  Hint (hidden := true) "Try `rw [Finset.prod_empty]`."
  rw [Finset.prod_empty]
  Hint (hidden := true) "The remaining `0 + 1 = 1` is arithmetic.
  Close with `omega`."
  omega

Conclusion "
The empty sum is `0` and the empty product is `1`, giving `0 + 1 = 1`.

This distinction matters whenever you reach a base case in a
recursive computation:
- Peeling a sum all the way down to `∅` gives `0`
- Peeling a product all the way down to `∅` gives `1`

**Memory aid**: the base case is always the *identity element*
for the operation. Adding `0` doesn't change a sum; multiplying
by `1` doesn't change a product.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto rfl
DisabledTheorem Finset.sum_pair Finset.prod_pair
