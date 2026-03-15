import GameServer.Commands
import Mathlib

World "BinomialTheorem"
Level 4

Title "Row sum from the binomial theorem"

Introduction
"
# Row Sum from the Binomial Theorem

You already know that $\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$ from the
BinomialCoefficients world (L08). Now you will see how this identity
*follows from* the binomial theorem.

## The idea

Set $x = 1$ and $y = 1$ in $(x + y)^n = \\sum_k x^k y^{n-k} \\binom{n}{k}$:

$$(1 + 1)^n = \\sum_{k=0}^{n} 1^k \\cdot 1^{n-k} \\cdot \\binom{n}{k} = \\sum_{k=0}^{n} \\binom{n}{k}$$

So $2^n = \\sum_{k=0}^{n} \\binom{n}{k}$.

## Your task

As a first step, apply `add_pow` with `x = 1, y = 1` in `ℕ` to
produce the binomial expansion of $(1 + 1)^n$.
"

/-- The binomial theorem specialized at x = 1, y = 1. -/
Statement (n : ℕ) :
    (1 + 1 : ℕ) ^ n = ∑ m ∈ Finset.range (n + 1), 1 ^ m * 1 ^ (n - m) * Nat.choose n m := by
  Hint "Apply `add_pow` with `x = 1` and `y = 1`.

  Try `exact add_pow 1 1 n`."
  Hint (hidden := true) "Try `exact add_pow 1 1 n`."
  exact add_pow 1 1 n

Conclusion
"
You specialized the binomial theorem at $x = 1, y = 1$.

## Reading the result

The equation is:

$$(1 + 1)^n = \\sum_{k=0}^{n} 1^k \\cdot 1^{n-k} \\cdot \\binom{n}{k}$$

Since $1^k = 1$ and $1^{n-k} = 1$, each term simplifies to just
$\\binom{n}{k}$. And $(1 + 1)^n = 2^n$.

So this is the row sum identity: $2^n = \\sum_{k=0}^{n} \\binom{n}{k}$.

## Transfer moment

On paper, the derivation is:

> *Set $x = 1, y = 1$ in the binomial theorem:*
> $$(1 + 1)^n = \\sum_{k=0}^{n} \\binom{n}{k} \\cdot 1^k \\cdot 1^{n-k} = \\sum_{k=0}^{n} \\binom{n}{k}$$
> *Hence $2^n = \\sum_{k=0}^{n} \\binom{n}{k}$.*

This is the standard \"algebraic proof\" of the row sum identity, as
opposed to the combinatorial proof (counting subsets by size).

## What comes next

The next level proves the row sum identity as a standalone result.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
