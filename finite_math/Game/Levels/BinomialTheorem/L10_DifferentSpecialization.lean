import Game.Metadata

World "BinomialTheorem"
Level 10

Title "A Different Specialization"

Introduction "
# Specializing with $y = 1$

In Level 8, you specialized `add_pow_nat` with $x = 1, y = 1$. Both
variable powers collapsed, and only `choose n m` survived.

Now try a different specialization: $y = 1$ but leave $x$ free.
The binomial theorem gives:

$$(x + 1)^n = \\sum_{m=0}^{n} x^m \\cdot 1^{n-m} \\cdot \\binom{n}{m}$$

Only the `y` power collapses: `1 ^ (n - m) = 1`. After removing
it with `one_pow` and `mul_one`, the summand becomes
`x ^ m * Nat.choose n m`.

But the target has `Nat.choose n m * x ^ m` — the factors are
in the **opposite order**. You need `mul_comm` to swap them.

**New element**: `mul_comm` inside `sum_congr`. After `one_pow`
and `mul_one` simplify the summand, `mul_comm` reorders the
remaining factors.
"

/-- Specializing the binomial theorem with y = 1. -/
Statement (x : ℕ) (n : ℕ) :
    (x + 1) ^ n =
      ∑ m ∈ Finset.range (n + 1), Nat.choose n m * x ^ m := by
  Hint "Start by expanding `(x + 1) ^ n` with the binomial theorem.
  Use `rw [add_pow_nat]` to rewrite the LHS."
  Hint (hidden := true) "Try `rw [add_pow_nat]`."
  rw [add_pow_nat]
  Hint "Good — both sides are now sums over the same range. The LHS
  summand is `x ^ m * 1 ^ (n - m) * Nat.choose n m` and the RHS
  summand is `Nat.choose n m * x ^ m`.

  Use `apply Finset.sum_congr rfl` to reduce to showing these are
  equal for each `m`."
  Hint (hidden := true) "Try `apply Finset.sum_congr rfl`."
  apply Finset.sum_congr rfl
  Hint "Introduce the bound variable."
  Hint (hidden := true) "Try `intro m _`."
  intro m _
  Hint "The goal is:
  `x ^ m * 1 ^ (n - m) * Nat.choose n m = Nat.choose n m * x ^ m`

  Strategy:
  1. `rw [one_pow]` simplifies `1 ^ (n - m)` to `1`
  2. `rw [mul_one]` removes the trailing `* 1` (note: `mul_one`,
     not `one_mul`, because the `1` is on the right)
  3. `rw [mul_comm]` swaps `x ^ m * choose n m` to `choose n m * x ^ m`"
  Hint (hidden := true) "Try `rw [one_pow, mul_one, mul_comm]`."
  rw [one_pow, mul_one, mul_comm]

Conclusion "
Three rewrites inside `sum_congr`: `one_pow, mul_one, mul_comm`.

**New move**: `mul_comm` inside a summand simplification. This is
needed whenever the target expression has factors in a different
order than what `add_pow` produces.

`add_pow` always produces `x^m * y^(n-m) * choose n m` — the
coefficient last. Many identities state them differently
(coefficient first), so you often need `mul_comm` after
simplification.

**The identity you proved**:
$$(x + 1)^n = \\sum_{m=0}^{n} \\binom{n}{m} \\cdot x^m$$

This is the standard 'polynomial expansion' form of the binomial
theorem with $y = 1$. The coefficients of the polynomial
$(x + 1)^n$ are exactly the binomial coefficients.

**The polynomial perspective**: This identity says that $\\binom{n}{m}$
is the coefficient of $x^m$ in the expansion of $(x+1)^n$. In other
words, the binomial coefficients *are* the polynomial coefficients —
this is the reason they are called 'coefficients' at all. This
connection between combinatorics and algebra runs deep: it is the
starting point for generating function methods.

**Numerical vs. polynomial specialization**: Levels 8 and 12 plug in
specific numbers for both $x$ and $y$, producing *numerical identities*
like $\\sum \\binom{n}{m} = 2^n$. This level is qualitatively different:
it keeps $x$ free and produces a *polynomial identity*. The distinction
matters — numerical specializations give counting formulas, while
polynomial specializations reveal what the coefficients *are*.

**What about specializing $x = 1$?** We specialized $y = 1$, leaving
$x$ free, giving the *ascending*-powers form. In the next level, you
will specialize $x = 1$, leaving $y$ free, to derive the
*descending*-powers form: $(1 + y)^n = \\sum \\binom{n}{m} y^{n-m}$.
The connection between the two forms turns out to be exactly the
symmetry $\\binom{n}{m} = \\binom{n}{n-m}$ from BinomialCoefficients.
"

/-- `mul_comm` states that `a * b = b * a`.

Multiplication is commutative — the order of factors does not matter.

## Syntax
```
rw [mul_comm]
rw [mul_comm a b]
```

## When to use it
When the goal has `a * b` but you need `b * a`, or when the factors
in a summand are in the wrong order after simplification. Common after
`one_pow` and `mul_one` leave `x ^ m * choose n m` but the target
expects `choose n m * x ^ m`.

## Tip
`rw [mul_comm]` rewrites the first match it finds. If there are
multiple products, use `rw [mul_comm a b]` with explicit arguments
to target the right one.
-/
TheoremDoc mul_comm as "mul_comm" in "Algebra"

TheoremTab "Choose"
NewTheorem mul_comm

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto ring ring_nf
