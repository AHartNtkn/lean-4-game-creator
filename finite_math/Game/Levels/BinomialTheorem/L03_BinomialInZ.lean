import GameServer.Commands
import Mathlib

World "BinomialTheorem"
Level 3

Title "The binomial theorem in ℤ"

Introduction
"
# The Binomial Theorem in ℤ

The binomial theorem works in any commutative semiring, including `ℤ`.
Working in `ℤ` (rather than `ℕ`) lets us use negative numbers, which
will be essential for identities like the alternating sum.

## Your task

Apply the binomial theorem in `ℤ` to prove:

$$(x + y)^n = \\sum_{k=0}^{n} x^k \\cdot y^{n-k} \\cdot \\binom{n}{k}$$

for arbitrary `x y : ℤ` and `n : ℕ`.

This is `add_pow` applied to integers.
"

/-- The binomial theorem for integers. -/
Statement (x y : ℤ) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * ↑(Nat.choose n m) := by
  Hint "This is a direct application of `add_pow`.

  Try `exact add_pow x y n`."
  Hint (hidden := true) "Try `exact add_pow x y n`."
  exact add_pow x y n

Conclusion
"
The binomial theorem is a single library call! The work lies in
*using* it — specializing `x` and `y` to derive identities.

## Why ℤ?

Working in `ℤ` lets us substitute negative values. For example:
- Setting `x = 1, y = -1` will give us the alternating sum identity
- Setting `x = -1, y = 2` will give us other useful identities

## The role of `↑`

Notice `↑(Nat.choose n m)` in the statement. The `↑` casts from `ℕ`
to `ℤ`. In `ℕ`, the cast is invisible (it's the identity), but in `ℤ`
it explicitly converts the natural number to an integer.

## What comes next

The next level specializes the binomial theorem to derive the
row sum identity.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
