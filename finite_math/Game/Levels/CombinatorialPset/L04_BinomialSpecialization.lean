import GameServer.Commands
import Mathlib

World "CombinatorialPset"
Level 4

Title "Binomial theorem specialization"

Introduction
"
# Specialization: $x = 1, y = 2$

In the BinomialTheorem world, you derived identities by substituting
specific values into the binomial theorem. Now do it with a fresh
substitution.

## The identity

Setting $x = 1, y = 2$ in $(x + y)^n = \\sum_k x^k y^{n-k} \\binom{n}{k}$:

$$(1 + 2)^n = \\sum_{k=0}^{n} 1^k \\cdot 2^{n-k} \\cdot \\binom{n}{k}$$

Since $1^k = 1$, each term simplifies to $2^{n-k} \\cdot \\binom{n}{k}$.
And $(1 + 2)^n = 3^n$.

So: $3^n = \\sum_{k=0}^{n} 2^{n-k} \\cdot \\binom{n}{k}$.

## Your task

Prove this identity by specializing `add_pow` and simplifying.
"

/-- Binomial theorem with x = 1, y = 2: 3^n = ∑ 1^k * 2^(n-k) * C(n,k). -/
Statement (n : ℕ) :
    3 ^ n = ∑ m ∈ Finset.range (n + 1), 1 ^ m * 2 ^ (n - m) * Nat.choose n m := by
  Hint (hidden := true) "The key insight: `3 = 1 + 2`, so `3 ^ n = (1 + 2) ^ n`.

  Apply the binomial theorem: `have h := add_pow 1 2 n`, then
  use `exact h` (or note that `3 ^ n` and `(1 + 2) ^ n` are
  definitionally equal in `ℕ`)."
  have h := add_pow 1 2 n
  exact h

Conclusion
"
You derived: $3^n = \\sum_{k=0}^{n} 2^{n-k} \\binom{n}{k}$.

## Checking for small $n$

For $n = 2$:
$$\\binom{2}{0} \\cdot 2^2 + \\binom{2}{1} \\cdot 2^1 + \\binom{2}{2} \\cdot 2^0$$
$$= 1 \\cdot 4 + 2 \\cdot 2 + 1 \\cdot 1 = 4 + 4 + 1 = 9 = 3^2 \\quad ✓$$

## Transfer moment

On paper: *\"Setting $x = 1, y = 2$ in the binomial theorem:*
*$(1 + 2)^n = \\sum_{k=0}^{n} 1^k \\cdot 2^{n-k} \\binom{n}{k} = \\sum_{k=0}^{n} 2^{n-k} \\binom{n}{k}$.*
*Since $(1+2)^n = 3^n$, we conclude $3^n = \\sum 2^{n-k} \\binom{n}{k}$. $\\square$\"*

## The method

You specialized the binomial theorem to specific values. This is the
same technique used in the BinomialTheorem world (L04 with $x=y=1$,
L10 with $x=-1, y=2$), now on a different substitution.

**Retrieval check**: Binomial theorem specialization (M29) on the
fresh substitution $(1, 2)$.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
