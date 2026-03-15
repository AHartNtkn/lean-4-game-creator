import GameServer.Commands
import Mathlib

World "BinomialTheorem"
Level 7

Title "Vandermonde: a concrete example"

Introduction
"
# Vandermonde's Identity: A Concrete Example

Let's verify Vandermonde's identity for specific values.

## The identity

With $m = 2, n = 3, k = 2$:

$$\\binom{2 + 3}{2} = \\sum_{j=0}^{2} \\binom{2}{j} \\cdot \\binom{3}{2-j}$$

The right-hand side expands to:

$$\\binom{2}{0}\\binom{3}{2} + \\binom{2}{1}\\binom{3}{1} + \\binom{2}{2}\\binom{3}{0}$$

$$= 1 \\cdot 3 + 2 \\cdot 3 + 1 \\cdot 1 = 3 + 6 + 1 = 10$$

And $\\binom{5}{2} = 10$. ✓

## Your task

Apply `Nat.add_choose_eq` to prove this specific instance.
"

/-- Vandermonde's identity for C(5, 2) = C(2+3, 2). -/
Statement : Nat.choose 5 2 = ∑ ij ∈ Finset.antidiagonal 2, Nat.choose 2 ij.1 * Nat.choose 3 ij.2 := by
  Hint "Note that `5 = 2 + 3`, so this is `Nat.add_choose_eq` with
  `m = 2`, `n = 3`, `k = 2`.

  Try `exact Nat.add_choose_eq 2 3 2`."
  Hint (hidden := true) "Try `exact Nat.add_choose_eq 2 3 2`."
  exact Nat.add_choose_eq 2 3 2

Conclusion
"
You verified Vandermonde's identity: $\\binom{5}{2} = 10$ as a
convolution over Pascal's triangle.

## The computation in detail

| $j$ | $\\binom{2}{j}$ | $\\binom{3}{2-j}$ | Product |
|-----|-----------------|-------------------|---------|
| 0 | 1 | 3 | 3 |
| 1 | 2 | 3 | 6 |
| 2 | 1 | 1 | 1 |
| **Total** | | | **10** |

## Special cases of Vandermonde

Setting $m = n$ and $k = n$ in Vandermonde gives:

$$\\binom{2n}{n} = \\sum_{j=0}^{n} \\binom{n}{j}^2$$

This is the \"sum of squares of a row\" identity for Pascal's triangle.

## What comes next

The next level tackles the **alternating sum** identity, which requires
working in `ℤ` because of the factor $(-1)^k$.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
