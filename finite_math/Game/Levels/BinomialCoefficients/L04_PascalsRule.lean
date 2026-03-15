import GameServer.Commands
import Mathlib

World "BinomialCoefficients"
Level 4

Title "Pascal's rule"

Introduction
"
# Pascal's Rule

Pascal's rule is the central recursion for binomial coefficients:

$$\\binom{n+1}{k+1} = \\binom{n}{k} + \\binom{n}{k+1}$$

You already used this as a *rewrite rule* in L01 to compute
$\\binom{5}{2}$. Now you will prove a general identity that
*follows from* Pascal's rule.

## The identity

Prove that for all $n$:

$$\\binom{n+1}{1} = \\binom{n}{0} + \\binom{n}{1}$$

This is Pascal's rule with $k = 0$. The left-hand side is $n+1$,
and the right-hand side is $1 + n = n+1$.

## Strategy

This is a direct application of `Nat.choose_succ_succ` with $k = 0$.
"

/-- Pascal's rule with k = 0: C(n+1, 1) = C(n, 0) + C(n, 1). -/
Statement (n : ℕ) : Nat.choose (n + 1) 1 = Nat.choose n 0 + Nat.choose n 1 := by
  Hint "This is a direct instance of Pascal's rule. Note that `1 = 0 + 1`,
  so `Nat.choose_succ_succ` applies with `k = 0`.

  Try `rw [Nat.choose_succ_succ]`."
  Hint (hidden := true) "Try `rw [Nat.choose_succ_succ]`. Lean will match
  `1` as `0 + 1` and apply the recursion."
  rw [Nat.choose_succ_succ]

Conclusion
"
The proof is a single rewrite — Pascal's rule is exactly this identity!

$$\\binom{n+1}{k+1} = \\binom{n}{k} + \\binom{n}{k+1}$$

With $k = 0$: $\\binom{n+1}{1} = \\binom{n}{0} + \\binom{n}{1} = 1 + n$.

## Why Pascal's rule matters

Pascal's rule is the *definition* of `Nat.choose` in Lean (along with
the boundary conditions). Every other identity about binomial coefficients
is ultimately proved by induction using this recursion.

## Combinatorial meaning

Consider a set $S$ with $n+1$ elements. Fix one element $x \\in S$.
The $k+1$-element subsets of $S$ split into two disjoint groups:
- Those that *include* $x$: choosing the remaining $k$ elements from
  the other $n$ elements gives $\\binom{n}{k}$ subsets.
- Those that *exclude* $x$: choosing all $k+1$ elements from the
  other $n$ elements gives $\\binom{n}{k+1}$ subsets.

Adding these gives Pascal's rule.

## What comes next

The next level uses Pascal's rule *in action* to compute specific
values by hand.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
