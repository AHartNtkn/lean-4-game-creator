import Game.Metadata

World "PascalsTriangle"
Level 16

Title "Boss: The Full Antidiagonal Sum"

Introduction "
# Boss: $\\sum_{(i,j)} \\left(\\binom{n}{i}^2 + \\binom{n}{i} + \\binom{n}{j}\\right) = \\binom{2n}{n} + 2 \\cdot 2^n$

For each pair $(i, j)$ in the antidiagonal of $n$, sum three
contributions:
- The **squared coefficient** $\\binom{n}{i}^2$
- The **first entry** $\\binom{n}{i}$
- The **second entry** $\\binom{n}{j}$

The total is $\\binom{2n}{n} + 2 \\cdot 2^n$ — the central binomial
coefficient plus twice the row sum.

**Why?** Split the sum into three parts using `sum_add_distrib`.
- The squared sum requires the **sum_congr pointwise reduction**
  (Level 15): reduce $\\binom{n}{i}^2$ to $\\binom{n}{i} \\cdot \\binom{n}{j}$
  using symmetry on the antidiagonal, then apply Vandermonde
- The first-entry sum is the row sum $= 2^n$
  (Level 7's reindexing pattern)
- The second-entry sum is the symmetric row sum $= 2^n$
  (Level 8's swap-reindex pattern)

**Skills needed**:
- `Finset.sum_add_distrib` — split a sum of sums (BigOpAlgebra)
- `Finset.sum_congr rfl` — reduce sum equation to pointwise (Level 15)
- `sq` — unfold squares to products (Level 15)
- `Nat.choose_symm` — symmetry on antidiagonal pairs (Level 14)
- `Nat.add_choose_eq` — Vandermonde identity (Level 10)
- `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` — reindex (Level 7)
- `← Finset.Nat.sum_antidiagonal_swap` — swap coordinates (Level 8)
- `Nat.sum_range_choose` — row sum identity (BinomialTheorem)
- `have` with sub-proofs — intermediate results
- `ring` — final arithmetic
"

/-- The full antidiagonal sum: combines symmetry reduction, Vandermonde, reindexing, and swap. -/
Statement (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n,
      (Nat.choose n p.1 ^ 2 + Nat.choose n p.1 + Nat.choose n p.2) =
    Nat.choose (2 * n) n + 2 * 2 ^ n := by
  Hint "The summand is a sum of three terms. Split it into three
  separate sums using `Finset.sum_add_distrib` twice."
  Hint (hidden := true) "Try `rw [Finset.sum_add_distrib]` to split off the last term."
  rw [Finset.sum_add_distrib]
  Hint (hidden := true) "Apply `rw [Finset.sum_add_distrib]` again to split the remaining two terms."
  rw [Finset.sum_add_distrib]
  Hint "Three sums plus arithmetic. The first sum has squares —
  use the Level 15 pattern (sum_congr + sq + choose_symm) to
  reduce it to a Vandermonde convolution. The other two sums
  use reindexing and swap-reindexing from Levels 7-8."
  Hint (hidden := true) "Start with the squared sum. State the result:
  `have h1 : ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.1 ^ 2 = Nat.choose (2 * n) n := by`"
  have h1 : ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.1 ^ 2 = Nat.choose (2 * n) n := by
    Hint "First reshape: `2 * n = n + n`, then expand using Vandermonde.
    This converts the RHS to a product sum that you can match
    term-by-term with the squared sum."
    Hint (hidden := true) "Try `have hh : 2 * n = n + n := by ring` then `rw [hh, Nat.add_choose_eq n n n]`."
    have hh : 2 * n = n + n := by ring
    rw [hh, Nat.add_choose_eq n n n]
    Hint "The goal is now:
    `∑ p, choose n p.1 ^ 2 = ∑ ij, choose n ij.1 * choose n ij.2`

    Use `Finset.sum_congr rfl` to reduce to a pointwise equation."
    Hint (hidden := true) "Try `apply Finset.sum_congr rfl`."
    apply Finset.sum_congr rfl
    Hint "Name the pair and its membership."
    Hint (hidden := true) "Try `intro p hp`."
    intro p hp
    Hint "Extract arithmetic from the membership, unfold the square,
    and apply symmetry — exactly as in Level 15."
    Hint (hidden := true) "Try `rw [Finset.mem_antidiagonal] at hp` then `rw [sq]`
    then `have h_eq : p.2 = n - p.1 := by omega`
    then `have h_le : p.1 ≤ n := by omega`
    then `rw [h_eq, Nat.choose_symm h_le]`."
    rw [Finset.mem_antidiagonal] at hp
    rw [sq]
    have h_eq : p.2 = n - p.1 := by omega
    have h_le : p.1 ≤ n := by omega
    rw [h_eq, Nat.choose_symm h_le]
  Hint "Now evaluate the second sum: the row sum via reindexing."
  Hint (hidden := true) "State the reindexing result:
  `have h2 : ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.1 = 2 ^ n := by`"
  have h2 : ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.1 = 2 ^ n := by
    Hint "Reindex to a range sum, then apply `sum_range_choose`."
    Hint (hidden := true) "Try `rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`."
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    Hint (hidden := true) "Try `exact Nat.sum_range_choose n`."
    exact Nat.sum_range_choose n
  Hint "Now evaluate the third sum: swap first, then reindex."
  Hint (hidden := true) "State the swap-reindex result:
  `have h3 : ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.2 = 2 ^ n := by`"
  have h3 : ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.2 = 2 ^ n := by
    Hint "Swap to convert `p.2` to `p.1`, then reindex."
    Hint (hidden := true) "Try `rw [← Finset.Nat.sum_antidiagonal_swap]`."
    rw [← Finset.Nat.sum_antidiagonal_swap]
    Hint (hidden := true) "Try `rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`."
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    Hint (hidden := true) "Try `exact Nat.sum_range_choose n`."
    exact Nat.sum_range_choose n
  Hint "Substitute all three results and simplify with `ring`."
  Hint (hidden := true) "Try `rw [h1, h2, h3]` then `ring`."
  rw [h1, h2, h3]
  Hint (hidden := true) "Try `ring`."
  ring

Conclusion "
You proved:
$$\\sum_{(i,j) \\in \\text{antidiagonal}(n)} \\left(\\binom{n}{i}^2 + \\binom{n}{i} + \\binom{n}{j}\\right) = \\binom{2n}{n} + 2 \\cdot 2^n$$

**Skills integrated in this boss**:
1. `Finset.sum_add_distrib` — split a sum of sums (BigOpAlgebra)
2. `Finset.sum_congr rfl` — reduce sum equation to pointwise (Level 15)
3. `sq` — unfold $a^2 = a \\cdot a$ (Level 15)
4. `Nat.choose_symm` — symmetry on antidiagonal pairs (Level 14)
5. `Nat.add_choose_eq` — the Vandermonde identity (Level 10)
6. `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` — reindex (Level 7)
7. `← Finset.Nat.sum_antidiagonal_swap` — swap pair coordinates (Level 8)
8. `Nat.sum_range_choose` — the row sum $\\sum \\binom{n}{k} = 2^n$ (BinomialTheorem)
9. `have` — three intermediate results
10. `ring` — final arithmetic

**The structure of the proof**: Split -> Evaluate each part -> Combine.
Three sub-proofs, each retrieving a different pattern:
- **h1** (squared sum): sum_congr reduction + symmetry + Vandermonde
  (Levels 14-15 pattern, then Level 10 reshape-flip-apply)
- **h2** (row sum): reindex + close (Level 7 pattern)
- **h3** (symmetric row sum): swap + reindex + close (Levels 8-9 pattern)

**What made h1 different**: Unlike Levels 7-9 where the summand
was already in a directly evaluable form, h1 required a
**transformation** step: reducing squares to products via
antidiagonal symmetry before Vandermonde could apply. This is the
integration of the symmetry arc (Levels 14-15) with the
sum-manipulation arc (Levels 7-12).
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add
