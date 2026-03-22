import Game.Metadata

World "PascalsTriangle"
Level 15

Title "The Sum of Squared Binomial Coefficients"

Introduction "
# Connecting Symmetry to Convolution

In Level 11, you proved:
$$\\sum_{(i,j) \\in \\text{antidiagonal}(n)} \\binom{n}{i} \\cdot \\binom{n}{j} = \\binom{2n}{n}$$

In Level 14, you proved the term-by-term symmetry:
$\\binom{n}{p_1} = \\binom{n}{p_2}$ on the antidiagonal.

Combining these: each product $\\binom{n}{i} \\cdot \\binom{n}{j}$ is
really $\\binom{n}{i}^2$. This gives one of the most beautiful
identities in combinatorics:

$$\\sum_{(i,j) \\in \\text{antidiagonal}(n)} \\binom{n}{i}^2 = \\binom{2n}{n}$$

**Your task**: Prove this identity by connecting it to Vandermonde.

**Proof plan**:
1. Rewrite `choose (2 * n) n` as the Vandermonde sum using `add_choose_eq`
   (reshape-flip-apply)
2. Reduce to term equality with `sum_congr rfl` — the
   **sum_congr pointwise reduction** pattern
3. Unfold `a ^ 2 = a * a` using the rewrite lemma `sq`
4. Show each squared term equals the corresponding product using
   `choose_symm` (exactly as in Level 14)
"

/-- `sq` states that `a ^ 2 = a * a`.

## Syntax
```
rw [sq]
```

## When to use it
When you see `a ^ 2` in the goal or a hypothesis and want to
convert it to `a * a` (or vice versa with `← sq`). Useful when
a goal involves squares but the relevant lemma speaks about
products.

## Example
```
-- goal: x ^ 2 = x * x
rw [sq]
-- goal becomes: x * x = x * x
```
-/
TheoremDoc sq as "sq" in "Algebra"

/-- The sum of squared binomial coefficients equals C(2n, n). -/
Statement (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n,
      Nat.choose n p.1 ^ 2 = Nat.choose (2 * n) n := by
  Hint "First, rewrite `2 * n` as `n + n` so it matches the
  Vandermonde identity's form. This is the start of the
  reshape-flip-apply pattern."
  Hint (hidden := true) "Try `have h : 2 * n = n + n := by ring`."
  have h : 2 * n = n + n := by ring
  Hint "Now rewrite the goal."
  Hint (hidden := true) "Try `rw [h]`."
  rw [h]
  Hint "Expand `(n + n).choose n` into its Vandermonde sum using
  `Nat.add_choose_eq`. This replaces the RHS with
  `∑ p ∈ antidiagonal n, choose n p.1 * choose n p.2`."
  Hint (hidden := true) "Try `rw [Nat.add_choose_eq n n n]`."
  rw [Nat.add_choose_eq n n n]
  Hint "Now the goal is:
  `∑ p ∈ antidiagonal n, choose n p.1 ^ 2 =
   ∑ p ∈ antidiagonal n, choose n p.1 * choose n p.2`

  These sums are equal term-by-term. Use `Finset.sum_congr rfl`
  to reduce from proving two sums equal to proving each term equal."
  Hint (hidden := true) "Try `apply Finset.sum_congr rfl`."
  apply Finset.sum_congr rfl
  Hint "**Checkpoint**: You reduced a sum equation to a pointwise
  equation. Name the pair and its membership with `intro p hp`."
  Hint (hidden := true) "Try `intro p hp`."
  intro p hp
  Hint "Extract the arithmetic from the membership: `p.1 + p.2 = n`."
  Hint (hidden := true) "Try `rw [Finset.mem_antidiagonal] at hp`."
  rw [Finset.mem_antidiagonal] at hp
  Hint "Unfold the square using `sq`: converts `choose n p.1 ^ 2`
  to `choose n p.1 * choose n p.1`."
  Hint (hidden := true) "Try `rw [sq]`."
  rw [sq]
  Hint "The goal is `choose n p.1 * choose n p.1 = choose n p.1 * choose n p.2`.
  You need `choose n p.1 = choose n p.2` — the symmetry from Level 14."
  Hint (hidden := true) "Try:
  `have h_eq : p.2 = n - p.1 := by omega`
  `have h_le : p.1 ≤ n := by omega`
  `rw [h_eq, Nat.choose_symm h_le]`"
  have h_eq : p.2 = n - p.1 := by omega
  have h_le : p.1 ≤ n := by omega
  rw [h_eq, Nat.choose_symm h_le]

Conclusion "
You proved:
$$\\sum_{(i,j) \\in \\text{antidiagonal}(n)} \\binom{n}{i}^2 = \\binom{2n}{n}$$

This is one of the most elegant identities in combinatorics.
It connects two themes from this world:

- **Symmetry** (Levels 2, 14): $\\binom{n}{k} = \\binom{n}{n-k}$
  lets you replace $\\binom{n}{j}$ with $\\binom{n}{i}$ when $i + j = n$

- **Convolution** (Level 11): the Vandermonde identity gives
  $\\sum \\binom{n}{i} \\cdot \\binom{n}{j} = \\binom{2n}{n}$

Combining them: each product $\\binom{n}{i} \\cdot \\binom{n}{j}$
is really $\\binom{n}{i}^2$, so the convolution sum is a sum of
squares.

**The sum_congr pointwise reduction pattern**: When two sums over
the same index set differ only term-by-term, use `sum_congr rfl`
to reduce the sum equation to a pointwise equation, then prove each
term matches. This pattern — `apply sum_congr rfl`, `intro p hp`,
then work on the single term — is a reusable proof strategy that
transfers to any setting where you need to show two sums are equal
by showing their summands agree.

**Note on the $k = n$ specialization**: The sum-of-squares identity
depends crucially on $k = n$ in Vandermonde. When $i + j = k \\neq n$,
the products $\\binom{n}{i} \\cdot \\binom{n}{j}$ are NOT all squares,
because $j \\neq n - i$.

**Concrete check**: For $n = 3$:
$$1^2 + 3^2 + 3^2 + 1^2 = 1 + 9 + 9 + 1 = 20 = \\binom{6}{3}$$
"

NewTheorem sq

TheoremTab "Algebra"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add
