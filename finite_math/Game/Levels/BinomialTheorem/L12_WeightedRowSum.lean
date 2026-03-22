import Game.Metadata

World "BinomialTheorem"
Level 12

Title "Weighted Row Sum"

Introduction "
# Weighted Sum: $\\sum \\binom{n}{m} \\cdot 2^m = 3^n$

Setting $x = 2$ and $y = 1$ in the binomial theorem gives:

$$(2 + 1)^n = \\sum_{m=0}^{n} 2^m \\cdot 1^{n-m} \\cdot \\binom{n}{m}$$

Simplifying: $3^n = \\sum \\binom{n}{m} \\cdot 2^m$.

This is a second application of the specialize-simplify-rewrite pattern
from Level 8, now with the `mul_comm` variation from Level 10.

**What you need**:
- `have h := add_pow_nat 2 1 n` — specialize the binomial theorem (Level 1)
- `have simpl : ...` — prove the pointwise simplification (Level 5 pattern)
  - `one_pow` — simplify `1 ^ (n - m)` (Level 4)
  - `mul_one` — remove trailing `* 1` (Level 4)
  - `mul_comm` — reorder factors (Level 10)
- `rw [Finset.sum_congr rfl simpl] at h` — apply to the hypothesis (Level 8 pattern)
- `exact h.symm` — close the goal (Level 6/8 pattern)
"

/-- The weighted row sum: sum of choose(n,m) * 2^m equals 3^n. -/
Statement (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), Nat.choose n m * 2 ^ m = 3 ^ n := by
  Hint "Start by specializing the binomial theorem to `x = 2, y = 1`.
  This gives you the expansion of `(2 + 1) ^ n`."
  Hint (hidden := true) "Try `have h := add_pow_nat 2 1 n`."
  have h := add_pow_nat 2 1 n
  Hint "Now `h` says `(2 + 1) ^ n = ∑ m, 2^m * 1^(n-m) * choose n m`.

  The summand `2^m * 1^(n-m) * choose n m` needs to become
  `choose n m * 2^m`. Set up the pointwise simplification."
  Hint (hidden := true) "Declare:
  `have simpl : ∀ m ∈ Finset.range (n + 1), 2 ^ m * 1 ^ (n - m) * Nat.choose n m = Nat.choose n m * 2 ^ m := by`

  Then: `intro m _` followed by `rw [one_pow, mul_one, mul_comm]`."
  have simpl : ∀ m ∈ Finset.range (n + 1),
      2 ^ m * 1 ^ (n - m) * Nat.choose n m = Nat.choose n m * 2 ^ m := by
    intro m _
    rw [one_pow, mul_one, mul_comm]
  Hint "Good — you have `simpl`. Now apply it to the sum in `h`."
  Hint (hidden := true) "Try `rw [Finset.sum_congr rfl simpl] at h`."
  rw [Finset.sum_congr rfl simpl] at h
  Hint "Now `h` says `(2 + 1) ^ n = ∑ m, choose n m * 2^m`.

  The goal is `∑ m, choose n m * 2^m = 3 ^ n`. Since `2 + 1 = 3`,
  `h.symm` gives exactly the goal."
  Hint (hidden := true) "Try `exact h.symm`."
  exact h.symm

Conclusion "
You proved the **weighted row sum**:

$$\\sum_{m=0}^{n} \\binom{n}{m} \\cdot 2^m = 3^n$$

This is the same specialize-simplify-rewrite pattern as Level 8
(the row sum), but with `x = 2` instead of `x = 1`. The extra
ingredient is `mul_comm` (Level 10) to reorder the factors.

**The counting interpretation**: Consider a set with $n$ elements.
For each element, you have 3 choices: exclude it (contributing
nothing), include it as 'type A' (contributing a factor of 2),
or include it as 'type B' (contributing a factor of 1). That is
$3^n$ total choices. Grouping by the number of included elements:
if $m$ elements are included, there are $\\binom{n}{m}$ ways to
choose them, and $2^m$ ways to assign them types. Summing gives
$\\sum \\binom{n}{m} \\cdot 2^m = 3^n$.

**So far**: You have derived two identities from `add_pow`:
- $x = y = 1$: $\\sum \\binom{n}{m} = 2^n$ (Level 8)
- $x = 2, y = 1$: $\\sum \\binom{n}{m} \\cdot 2^m = 3^n$ (this level)

Both used the same proof skeleton over $\\mathbb{N}$. Can we push
further? What happens with $x = -1$? That requires working over
$\\mathbb{Z}$ — which is exactly where we go next.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto ring ring_nf
