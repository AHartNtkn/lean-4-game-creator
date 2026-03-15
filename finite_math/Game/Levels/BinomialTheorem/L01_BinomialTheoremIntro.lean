import GameServer.Commands
import Mathlib

World "BinomialTheorem"
Level 1

Title "The binomial theorem"

Introduction
"
# The Binomial Theorem

Welcome to the **Binomial Theorem** world! The binomial theorem
expresses the expansion of $(a + b)^n$ as a sum involving binomial
coefficients:

$$(a + b)^n = \\sum_{k=0}^{n} a^k \\cdot b^{n-k} \\cdot \\binom{n}{k}$$

## In Lean

The mathlib lemma `add_pow` states exactly this:

```
add_pow (x y : R) (n : ℕ) :
  (x + y) ^ n = ∑ m ∈ Finset.range (n + 1),
    x ^ m * y ^ (n - m) * ↑(Nat.choose n m)
```

Here `↑(Nat.choose n m)` is the cast of the binomial coefficient from
`ℕ` into the ambient ring `R`. When `R = ℕ`, the cast is the identity.

## Your task

Verify the binomial theorem for the concrete case $(2 + 3)^2 = 25$
by expressing both sides in terms of the sum formula.

Apply `add_pow` with `x = 2`, `y = 3`, `n = 2` in `ℕ`.
"

/-- Verify the binomial theorem for (2 + 3)² in ℕ. -/
Statement : (2 + 3 : ℕ) ^ 2 = ∑ m ∈ Finset.range 3, 2 ^ m * 3 ^ (2 - m) * Nat.choose 2 m := by
  Hint "The mathlib lemma `add_pow` states the binomial theorem. Since
  `Finset.range 3 = Finset.range (2 + 1)`, it applies directly.

  Try `exact add_pow 2 3 2`."
  Hint (hidden := true) "Try `exact add_pow 2 3 2`."
  exact add_pow 2 3 2

Conclusion
"
You applied the binomial theorem to verify:

$$(2 + 3)^2 = \\sum_{k=0}^{2} 2^k \\cdot 3^{2-k} \\cdot \\binom{2}{k}$$

$$= 2^0 \\cdot 3^2 \\cdot 1 + 2^1 \\cdot 3^1 \\cdot 2 + 2^2 \\cdot 3^0 \\cdot 1$$

$$= 9 + 12 + 4 = 25 = 5^2 \\quad ✓$$

## Reading the sum

The sum `∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * ↑(choose n m)`
ranges over `m = 0, 1, …, n`. Each term has:
- `x ^ m` — the power of `x`
- `y ^ (n - m)` — the complementary power of `y`
- `↑(choose n m)` — the binomial coefficient, cast into the ring

## What comes next

The next level introduces `push_cast`, a tactic for handling the
cast `↑` that appears when working with binomial coefficients in
rings other than `ℕ`.
"

/-- `add_pow` is the binomial theorem:
`(x + y) ^ n = ∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * ↑(Nat.choose n m)`.

This holds in any commutative semiring. -/
TheoremDoc add_pow as "add_pow" in "Nat"

NewTheorem add_pow
DisabledTactic trivial decide native_decide simp aesop simp_all
