import Game.Metadata

World "PascalsTriangle"
Level 9

Title "The Double Row Sum"

Introduction "
# Combining Swap and Reindex

In Levels 7-8, you proved:
- $\\sum_{(i,j)} \\binom{n}{i} = 2^n$ (reindex)
- $\\sum_{(i,j)} \\binom{n}{j} = 2^n$ (swap + reindex)

Now combine them. For each pair $(i, j)$ in the antidiagonal,
sum **both** binomial coefficients $\\binom{n}{i} + \\binom{n}{j}$.
The result is $2 \\cdot 2^n$ — twice the row sum.

**Proof plan**:
1. Use `Finset.sum_add_distrib` to split the sum of sums into two sums
2. Evaluate each half with `have` sub-proofs
   - The first uses reindexing (Level 7 pattern)
   - The second uses swap + reindexing (Level 8 pattern)
3. Substitute and close with `ring`

This is a **rehearsal** for the boss, which adds a third component.
"

/-- The double row sum: ∑ (C(n,i) + C(n,j)) over the antidiagonal = 2 * 2^n. -/
Statement (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n,
      (Nat.choose n p.1 + Nat.choose n p.2) = 2 * 2 ^ n := by
  Hint "The summand is a sum of two terms. Split it into two
  separate sums using `Finset.sum_add_distrib`."
  Hint (hidden := true) "Try `rw [Finset.sum_add_distrib]`."
  rw [Finset.sum_add_distrib]
  Hint "Good — two sums. Evaluate each one as an intermediate result.
  The first sum uses reindexing (Level 7), the second uses
  swap + reindexing (Level 8)."
  Hint (hidden := true) "Introduce the first sum:
  `have h1 : ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.1 = 2 ^ n := by`
  then `rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`
  then `exact Nat.sum_range_choose n`."
  have h1 : ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.1 = 2 ^ n := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact Nat.sum_range_choose n
  Hint "Now introduce the second sum using the swap-reindex pattern."
  Hint (hidden := true) "Introduce the second sum:
  `have h2 : ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.2 = 2 ^ n := by`
  then `rw [← Finset.Nat.sum_antidiagonal_swap]`
  then `rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`
  then `exact Nat.sum_range_choose n`."
  have h2 : ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.2 = 2 ^ n := by
    rw [← Finset.Nat.sum_antidiagonal_swap]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact Nat.sum_range_choose n
  Hint "Substitute both results and simplify."
  Hint (hidden := true) "Try `rw [h1, h2]` then `ring`."
  rw [h1, h2]
  ring

Conclusion "
You proved:
$$\\sum_{(i,j) \\in \\text{antidiagonal}(n)} \\left(\\binom{n}{i} + \\binom{n}{j}\\right) = 2 \\cdot 2^n$$

**The decompose-evaluate-combine pattern**:
1. **Decompose** — `sum_add_distrib` splits the sum of sums
2. **Evaluate** — `have` sub-proofs compute each sum
3. **Combine** — `rw` and `ring` assemble the final result

Each sub-proof retrieves a pattern from a previous level:
- **h1** uses reindex + row sum (Level 7)
- **h2** uses swap + reindex + row sum (Level 8)

This three-phase pattern is exactly what the boss level
requires — but with an additional Vandermonde component.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
DisabledTheorem Nat.add_choose_eq
