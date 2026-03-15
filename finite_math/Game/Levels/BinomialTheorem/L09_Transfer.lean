import GameServer.Commands
import Mathlib

World "BinomialTheorem"
Level 9

Title "Transfer: the binomial theorem on ℕ"

Introduction
"
# Transfer: The Binomial Theorem on ℕ

Throughout this world you have used the binomial theorem in `ℤ` and
applied library lemmas. Now state the theorem one final time, purely
over `ℕ`, as a transfer exercise.

## The ordinary statement

On paper, the binomial theorem says:

$$(a + b)^n = \\sum_{k=0}^{n} \\binom{n}{k} \\cdot a^k \\cdot b^{n-k}$$

In Lean over `ℕ`, this is `add_pow a b n`.

## Transfer moment

Write out the binomial theorem as you would on a chalkboard:

> **Theorem** (Binomial Theorem). *For all non-negative integers $a, b$
> and all $n \\ge 0$:*
>
> $$(a + b)^n = \\sum_{k=0}^{n} \\binom{n}{k} \\, a^k \\, b^{n-k}$$
>
> *Proof.* By induction on $n$ using Pascal's rule
> $\\binom{n+1}{k+1} = \\binom{n}{k} + \\binom{n}{k+1}$. $\\square$

## Your task

Prove the binomial theorem for natural numbers using `add_pow`.
"

/-- The binomial theorem for natural numbers. -/
Statement (a b : ℕ) (n : ℕ) :
    (a + b) ^ n = ∑ k ∈ Finset.range (n + 1), a ^ k * b ^ (n - k) * Nat.choose n k := by
  Hint "Apply `add_pow` directly.

  Try `exact add_pow a b n`."
  Hint (hidden := true) "Try `exact add_pow a b n`."
  exact add_pow a b n

Conclusion
"
## The binomial theorem: a summary

You have now seen the binomial theorem from multiple angles:

| Level | What you did |
|-------|-------------|
| L01 | Applied `add_pow` to a concrete numerical example |
| L03 | Applied `add_pow` in `ℤ` (general `x, y`) |
| L04 | Specialized at $x = y = 1$ to derive the row sum |
| L09 | Stated the theorem over `ℕ` as a transfer exercise |

## Key identities derived from the binomial theorem

| Substitution | Identity |
|-------------|---------|
| $x = y = 1$ | $\\sum \\binom{n}{k} = 2^n$ |
| $x = 1, y = -1$ | $\\sum (-1)^k \\binom{n}{k} = 0$ for $n \\ge 1$ |

## Transfer: the inductive proof

The proof of the binomial theorem proceeds by induction on $n$:

1. **Base case** ($n = 0$): $(a + b)^0 = 1$, and the sum has one term
   $a^0 b^0 \\binom{0}{0} = 1$. ✓

2. **Inductive step**: Assume the theorem holds for $n$. Then
   $(a + b)^{n+1} = (a + b)(a + b)^n$. Distribute, use the inductive
   hypothesis, and recombine using Pascal's rule
   $\\binom{n+1}{k+1} = \\binom{n}{k} + \\binom{n}{k+1}$.

The formal proof in mathlib follows exactly this structure.

## What comes next

The boss level combines the binomial theorem with algebraic manipulation.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
