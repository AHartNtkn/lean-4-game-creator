import Game.Metadata

World "PsetCombinatorics"
Level 12

Title "Antidiagonal Double Sum"

Introduction "
# Both Coordinates at Once

In the PascalsTriangle world, you learned that the antidiagonal
indexes pairs $(i, j)$ with $i + j = n$, and that the **swap
lemma** lets you exchange the roles of the two coordinates.

Use these tools to evaluate the double row sum:

$$\\sum_{(i,j) \\in \\text{antidiagonal}(n)}
\\left(\\binom{n}{i} + \\binom{n}{j}\\right) = 2 \\cdot 2^n$$

**Strategy** (split-and-evaluate):
1. Split the sum of sums with `Finset.sum_add_distrib`
2. Show each half equals $2^n$ (the first via reindexing, the
   second via swap-reindex from PascalsTriangle Level 8)
3. Substitute and close
"

/-- The antidiagonal double row sum: ∑ (choose n p.1 + choose n p.2) = 2 * 2^n. -/
Statement (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n,
      (Nat.choose n p.1 + Nat.choose n p.2) = 2 * 2 ^ n := by
  Hint "The summand is a sum of two terms. Split into two separate
  sums using `Finset.sum_add_distrib`."
  Hint (hidden := true) "Try `rw [Finset.sum_add_distrib]`."
  rw [Finset.sum_add_distrib]
  Hint "The goal is
  `(∑ p, choose n p.1) + (∑ p, choose n p.2) = 2 * 2^n`.

  Show each sum equals `2^n` separately, then combine.

  For the first sum (`p.1`): reindex to a range sum and apply
  the row sum identity."
  Hint (hidden := true) "Declare:
  `have h1 : ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.1 = 2 ^ n := by`

  Then: `rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.sum_range_choose]`."
  have h1 : ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.1 = 2 ^ n := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.sum_range_choose]
  Hint "Now show the second sum (`p.2`) also equals `2^n`.

  Use the **swap-reindex** pattern from PascalsTriangle Level 8:
  `← sum_antidiagonal_swap` converts `p.2` into `p.1` (via
  `p.swap`), then reindex and apply the row sum."
  Hint (hidden := true) "Declare:
  `have h2 : ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.2 = 2 ^ n := by`

  Then:
  `rw [← Finset.Nat.sum_antidiagonal_swap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`
  `exact Nat.sum_range_choose n`"
  have h2 : ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.2 = 2 ^ n := by
    rw [← Finset.Nat.sum_antidiagonal_swap,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact Nat.sum_range_choose n
  Hint "Both sums are `2^n`. Substitute and close."
  Hint (hidden := true) "Try `rw [h1, h2]` then `ring`."
  rw [h1, h2]
  ring

Conclusion "
Split, evaluate each half, combine. The antidiagonal indexes
pairs $(i, j)$ with $i + j = n$ — exactly the Cauchy product
index set. The boss uses this: Vandermonde is a Cauchy product
of $(1+x)^n$ with itself.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add
