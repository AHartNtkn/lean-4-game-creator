import Game.Metadata

World "BinomialTheorem"
Level 15

Title "Boss: The Alternating Sum"

Introduction "
# Boss: $\\sum (-1)^m \\binom{n}{m} = 0$

The alternating sum of row $n$ of Pascal's triangle is zero (for $n \\geq 1$):

$$\\sum_{m=0}^{n} (-1)^m \\binom{n}{m} = 0$$

This is the most surprising consequence of the binomial theorem.
Each row of Pascal's triangle sums to $2^n$ (Level 8), but the
*alternating* sum — adding and subtracting alternate entries —
cancels perfectly to zero.

The proof: specialize `add_pow` to $x = -1, y = 1$ over $\\mathbb{Z}$:

$$((-1) + 1)^n = \\sum_{m=0}^{n} (-1)^m \\cdot 1^{n-m} \\cdot \\binom{n}{m}$$

The left side is $0^n = 0$. The right side simplifies to
$\\sum (-1)^m \\binom{n}{m}$.

**What you need**:
- `have h := add_pow (-1 : ℤ) 1 n` — specialize over ℤ (Level 1 pattern)
- `have simpl : ...` — simplify summands: `one_pow`, `mul_one` (Level 5 pattern)
- `rw [Finset.sum_congr rfl simpl] at h` — rewrite the sum (Level 8 pattern)
- `have h0 : (-1 : ℤ) + 1 = 0 := by omega` — arithmetic fact (Level 13)
- `rw [h0, zero_pow (by omega)] at h` — collapse the LHS (Level 13)
- `exact h.symm` — flip and close (Level 6)
"

/-- The alternating row sum of Pascal's triangle is zero. -/
Statement (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Finset.range (n + 1), (-1 : ℤ) ^ m * ↑(Nat.choose n m) = 0 := by
  Hint "Start by specializing `add_pow` to `x = -1, y = 1` over ℤ.
  Note: here we use `add_pow` directly (not `add_pow_nat`), because
  we are working over ℤ, not ℕ."
  Hint (hidden := true) "Try `have h := add_pow (-1 : ℤ) 1 n`."
  have h := add_pow (-1 : ℤ) 1 n
  Hint "Now `h` says `(-1 + 1)^n = ∑ m, (-1)^m * 1^(n-m) * ↑(choose n m)`.

  The summand needs simplifying. The `1^(n-m)` factor collapses as before.
  Set up the pointwise simplification with `have simpl : ...`."
  Hint (hidden := true) "Declare:
  `have simpl : ∀ m ∈ Finset.range (n + 1), (-1 : ℤ) ^ m * (1 : ℤ) ^ (n - m) * ↑(Nat.choose n m) = (-1 : ℤ) ^ m * ↑(Nat.choose n m) := by`

  Then: `intro m _` followed by `rw [one_pow, mul_one]`."
  have simpl : ∀ m ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ m * (1 : ℤ) ^ (n - m) * ↑(Nat.choose n m) =
      (-1 : ℤ) ^ m * ↑(Nat.choose n m) := by
    intro m _
    rw [one_pow, mul_one]
  Hint "Good — now apply the simplification to the sum in `h`."
  Hint (hidden := true) "Try `rw [Finset.sum_congr rfl simpl] at h`."
  rw [Finset.sum_congr rfl simpl] at h
  Hint "Now `h` says `(-1 + 1)^n = ∑ m, (-1)^m * ↑(choose n m)`.

  The right side matches the goal's left side. You need to simplify
  the left side of `h`: `(-1 + 1) = 0` and `0^n = 0` (since `n ≥ 1`).

  First establish `(-1 : ℤ) + 1 = 0` and rewrite."
  Hint (hidden := true) "Try:
  `have h0 : (-1 : ℤ) + 1 = 0 := by omega`
  `rw [h0, zero_pow (by omega)] at h`"
  have h0 : (-1 : ℤ) + 1 = 0 := by omega
  rw [h0, zero_pow (by omega)] at h
  Hint "Now `h` says `0 = ∑ m, (-1)^m * ↑(choose n m)`.
  The goal is `∑ ... = 0`. Flip `h` with `.symm` and close."
  Hint (hidden := true) "Try `exact h.symm`."
  exact h.symm

Conclusion "
You proved the **alternating sum identity**:

$$\\sum_{m=0}^{n} (-1)^m \\binom{n}{m} = 0 \\qquad (n \\geq 1)$$

Row 4 of Pascal's triangle is $1, 4, 6, 4, 1$. The alternating sum
$1 - 4 + 6 - 4 + 1 = 0$. Every row (except row 0) has this property.

**The identity manufacturing machine**: The binomial theorem is a
single identity that generates an infinite family of results by
specialization. You have now seen three instances:

| Inputs | LHS | Identity |
|---|---|---|
| $x = y = 1$ over $\\mathbb{N}$ | $2^n$ | $\\sum \\binom{n}{m} = 2^n$ (Level 8) |
| $x = 2, y = 1$ over $\\mathbb{N}$ | $3^n$ | $\\sum \\binom{n}{m} \\cdot 2^m = 3^n$ (Level 12) |
| $x = -1, y = 1$ over $\\mathbb{Z}$ | $0^n$ | $\\sum (-1)^m \\binom{n}{m} = 0$ (this level) |

These are all **numerical specializations** — both $x$ and $y$ are
specific numbers. Level 10 showed a different flavor: $y = 1$ with
$x$ free, producing the **polynomial identity**
$(x+1)^n = \\sum \\binom{n}{m} x^m$, revealing that binomial
coefficients *are* polynomial coefficients.

Setting $y = 1$ and $x = k - 1$ gives $k^n = \\sum \\binom{n}{m}(k-1)^m$
for any $k$. This is an **identity manufacturing machine**: one
theorem, infinitely many outputs, each a different counting identity.

**What changed in this proof**: The proof skeleton was the same
specialize-simplify-rewrite pattern, but two things were new:
1. **Type change**: `add_pow` over ℤ instead of `add_pow_nat` over ℕ,
   because $-1 \\notin \\mathbb{N}$
2. **LHS collapse**: the extra steps `omega` + `zero_pow` to simplify
   $(-1 + 1)^n$ to $0$, which the ℕ proofs did not need

The pattern is robust enough to survive a change of number system.

**Connection to inclusion-exclusion**: The alternating sum
$\\sum (-1)^m \\binom{n}{m} = 0$ is a special case of the
inclusion-exclusion principle. Given $n$ sets whose union is
the whole space, the alternating sum of intersection sizes
telescopes to zero. The binomial coefficients count the ways
to choose which intersections to include. This connects the
algebraic identity you just proved to a fundamental counting
principle.

**A caveat**: Not every binomial coefficient identity arises from
specializing `add_pow`. For example, Vandermonde's identity
$\\binom{m+n}{r} = \\sum_k \\binom{m}{k}\\binom{n}{r-k}$ requires
a different proof technique entirely. Specialization is powerful
but not universal.

**Looking ahead**: The binomial theorem generalizes to the
**multinomial theorem** for sums of more than two terms:
$(x_1 + x_2 + \\cdots + x_k)^n$. The multinomial coefficients
generalize the binomial coefficients, and the same
specialize-simplify-rewrite method applies.
"

/-- `Int.alternating_sum_range_choose` states that
`∑ m ∈ Finset.range (n + 1), (-1) ^ m * ↑(Nat.choose n m) = if n = 0 then 1 else 0`.

This is the Mathlib version of the alternating row sum identity.
For `n ≥ 1`, the sum equals `0`.
-/
TheoremDoc Int.alternating_sum_range_choose as "Int.alternating_sum_range_choose" in "Choose"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto ring ring_nf
DisabledTheorem Int.alternating_sum_range_choose
