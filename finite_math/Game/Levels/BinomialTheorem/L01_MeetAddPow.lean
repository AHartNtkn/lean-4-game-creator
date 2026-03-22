import Game.Metadata

World "BinomialTheorem"
Level 1

Title "The Binomial Theorem"

Introduction "
# Meet `add_pow`

The **binomial theorem** says:

$$(x + y)^n = \\sum_{m=0}^{n} x^m \\cdot y^{n-m} \\cdot \\binom{n}{m}$$

In Lean, this is the theorem `add_pow`:

```
add_pow (x y : R) (n : ℕ) :
  (x + y) ^ n =
    ∑ m ∈ Finset.range (n + 1),
      x ^ m * y ^ (n - m) * Nat.choose n m
```

Each summand has three factors:
- `x ^ m` — the power of `x` (from 0 to n)
- `y ^ (n - m)` — the complementary power of `y`
- `Nat.choose n m` — the binomial coefficient, counting how many
  of the $n$ factors contribute an $x$

Notice the factor order: `x ^ m * y ^ (n - m) * Nat.choose n m`.
The binomial coefficient appears last, multiplied into the product
of powers.

**Your task**: Apply `add_pow` to prove the binomial expansion
over natural numbers. This is a first-contact level — the theorem
does all the work.
"

/-- The binomial theorem for natural numbers. -/
Statement (x y : ℕ) (n : ℕ) :
    (x + y) ^ n =
      ∑ m ∈ Finset.range (n + 1),
        x ^ m * y ^ (n - m) * Nat.choose n m := by
  Hint "The goal is exactly the statement of `add_pow` applied to
  natural numbers. Close it with `exact add_pow x y n`."
  Hint (hidden := true) "Try `exact add_pow x y n`."
  exact add_pow x y n

Conclusion "
One step: `exact add_pow x y n`.

The binomial theorem is a **generating identity**: by plugging
in specific values of `x` and `y`, it produces many identities
for free. The classic example: setting `x = y = 1` gives

$$(1 + 1)^n = \\sum_{m=0}^{n} 1^m \\cdot 1^{n-m} \\cdot \\binom{n}{m}$$

The left side is $2^n$. The right side simplifies to
$\\sum \\binom{n}{m}$. So the sum of row $n$ of Pascal's triangle
is $2^n$. You will derive this identity in Level 8.

But first: what does the binomial theorem look like for a specific
small value of $n$? The next level shows you the most familiar case.

**Technical note**: `add_pow` works for any commutative semiring.
When we specialize to natural numbers and use `rw` or `sum_congr`
(instead of `exact`), we need `add_pow_nat` — a version that
avoids a type coercion issue. You will see this starting in Level 6.
"

/-- `add_pow` states that
`(x + y) ^ n = ∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * Nat.choose n m`.

The **binomial theorem**: the expansion of a power of a sum.

## Syntax
```
exact add_pow x y n
rw [add_pow]
have h := add_pow x y n
```

## When to use it
When you see `(x + y) ^ n` and want to expand it into a sum
involving binomial coefficients, or when you want to specialize
it to particular values of `x` and `y` to derive counting identities.

## Example
```
have h := add_pow (1 : ℕ) 1 n
-- h : (1 + 1) ^ n = ∑ m ∈ range (n+1), 1^m * 1^(n-m) * choose n m
```

## Warning
The summand order is `x^m * y^(n-m) * choose n m`, not
`choose n m * x^m * y^(n-m)`. You may need `mul_comm` to
reorder terms after simplification.
-/
TheoremDoc add_pow as "add_pow" in "Choose"

/-- `add_pow_nat` states that
`(x + y) ^ n = ∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * Nat.choose n m`
for natural numbers `x`, `y`, `n`.

This is the same as `add_pow` but specialized to `ℕ`. Use this
instead of `add_pow` when you need `rw` or `Finset.sum_congr` to
work with the resulting sum — `add_pow` introduces a type coercion
that blocks syntactic rewriting.

## Syntax
```
have h := add_pow_nat x y n
rw [add_pow_nat]
```

## When to use it
Whenever you would use `add_pow` but plan to rewrite the summand
afterward (e.g., with `sum_congr`).
-/
TheoremDoc add_pow_nat as "add_pow_nat" in "Choose"

TheoremTab "Choose"
NewTheorem add_pow add_pow_nat

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto
DisabledTheorem Nat.sum_range_choose
