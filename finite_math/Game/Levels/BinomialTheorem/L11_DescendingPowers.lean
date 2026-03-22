import Game.Metadata

World "BinomialTheorem"
Level 11

Title "The Descending-Powers Form"

Introduction "
# Specializing with $x = 1$

In Level 10, you specialized $y = 1$ (leaving $x$ free) and obtained
the **ascending-powers** form:

$$(x + 1)^n = \\sum_{m=0}^{n} \\binom{n}{m} \\cdot x^m$$

The binomial coefficients multiply **ascending** powers of $x$:
$x^0, x^1, \\ldots, x^n$.

Now try the mirror image: specialize $x = 1$ (leaving $y$ free).
The binomial theorem gives:

$$(1 + y)^n = \\sum_{m=0}^{n} 1^m \\cdot y^{n-m} \\cdot \\binom{n}{m}$$

After simplifying (with `one_pow` and `one_mul`), the $1^m$ factor
disappears and the summand becomes $\\binom{n}{m} \\cdot y^{n-m}$.

The binomial coefficients now multiply **descending** powers of $y$:
$y^n, y^{n-1}, \\ldots, y^0$.

**Why both forms agree**: $(x + 1)^n$ and $(1 + y)^n$ are the same
polynomial (just rename the variable). The ascending form has
coefficient $\\binom{n}{m}$ on $x^m$. The descending form has
coefficient $\\binom{n}{m}$ on $y^{n-m}$. Matching the coefficient
of the $k$-th power in both forms gives
$\\binom{n}{k} = \\binom{n}{n-k}$ — the symmetry identity you proved
in BinomialCoefficients.

**Proof plan**: Same as Level 10, with `x = 1` instead of `y = 1`.
"

/-- The descending-powers form of the binomial theorem. -/
Statement (y : ℕ) (n : ℕ) :
    (1 + y) ^ n =
      ∑ m ∈ Finset.range (n + 1), Nat.choose n m * y ^ (n - m) := by
  Hint "Start by expanding `(1 + y) ^ n` with the binomial theorem.
  Use `rw [add_pow_nat]` to rewrite the LHS."
  Hint (hidden := true) "Try `rw [add_pow_nat]`."
  rw [add_pow_nat]
  Hint "Good — both sides are now sums over the same range. The LHS
  summand is `1 ^ m * y ^ (n - m) * Nat.choose n m` and the RHS
  summand is `Nat.choose n m * y ^ (n - m)`.

  Use `apply Finset.sum_congr rfl` to reduce to showing these are
  equal for each `m`."
  Hint (hidden := true) "Try `apply Finset.sum_congr rfl`."
  apply Finset.sum_congr rfl
  Hint "Introduce the bound variable."
  Hint (hidden := true) "Try `intro m _`."
  intro m _
  Hint "The goal is:
  `1 ^ m * y ^ (n - m) * Nat.choose n m = Nat.choose n m * y ^ (n - m)`

  Strategy:
  1. `rw [one_pow]` simplifies `1 ^ m` to `1`
  2. `rw [one_mul]` removes the leading `1 *`
  3. `rw [mul_comm]` swaps `y ^ (n - m) * choose n m` to
     `choose n m * y ^ (n - m)`"
  Hint (hidden := true) "Try `rw [one_pow, one_mul, mul_comm]`."
  rw [one_pow, one_mul, mul_comm]

Conclusion "
Three rewrites inside `sum_congr`: `one_pow, one_mul, mul_comm`.

**Ascending vs. descending powers**: You have now proved both
polynomial forms of the binomial theorem:

| Specialization | Identity | Powers |
|---|---|---|
| $y = 1$ (Level 10) | $(x+1)^n = \\sum \\binom{n}{m} x^m$ | ascending: $x^0, x^1, \\ldots$ |
| $x = 1$ (this level) | $(1+y)^n = \\sum \\binom{n}{m} y^{n-m}$ | descending: $y^n, y^{n-1}, \\ldots$ |

Both say the same thing: the coefficients of the polynomial
$(1 + t)^n$ are the binomial coefficients. But they index them
differently — one uses the exponent $m$, the other uses $n - m$.

**The symmetry connection**: Comparing the coefficient of $t^k$
in both forms:
- Ascending form: the coefficient of $t^k$ is $\\binom{n}{k}$
- Descending form: the coefficient of $t^k$ is $\\binom{n}{n-k}$

Since these are coefficients of the same polynomial, they must be
equal: $\\binom{n}{k} = \\binom{n}{n-k}$. This is exactly the
**symmetry identity** you proved in BinomialCoefficients. The two
polynomial forms are equivalent *because of* this symmetry — and
conversely, the symmetry of binomial coefficients *is* the statement
that these two forms agree.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto ring ring_nf
