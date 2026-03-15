import GameServer.Commands
import Mathlib

World "PascalsTriangle"
Level 5

Title "Symmetry visible in Row 4"

Introduction
"
# Symmetry Visible

Look at Row 4 of Pascal's triangle:

$$1, \\quad 4, \\quad 6, \\quad 4, \\quad 1$$

Reading left to right: $1, 4, 6, 4, 1$.
Reading right to left: $1, 4, 6, 4, 1$.

The row is **symmetric** — it reads the same in both directions!

## The symmetry identity

This is the concrete face of the abstract identity
$\\binom{n}{k} = \\binom{n}{n-k}$, which you proved in the
Binomial Coefficients world using `Nat.choose_symm`.

For Row 4, the symmetry pairs are:
- $\\binom{4}{0} = \\binom{4}{4} = 1$ (both endpoints)
- $\\binom{4}{1} = \\binom{4}{3} = 4$ (inner pair)
- $\\binom{4}{2} = \\binom{4}{2} = 6$ (middle, paired with itself)

## Your task

Prove the inner symmetry pair: $\\binom{4}{1} = \\binom{4}{3}$.

This concretizes `Nat.choose_symm` with $n = 4, k = 1$:
$\\binom{4}{3} = \\binom{4}{4-1} = \\binom{4}{1}$.
"

/-- Row 4 symmetry: C(4, 1) = C(4, 3). -/
Statement : Nat.choose 4 1 = Nat.choose 4 3 := by
  Hint "To use `Nat.choose_symm`, recall its statement:

  `Nat.choose_symm (h : k ≤ n) : Nat.choose n (n - k) = Nat.choose n k`

  It rewrites `choose n (n - k)` to `choose n k`. So
  `Nat.choose_symm` with `k = 1` gives `Nat.choose 4 (4 - 1) = Nat.choose 4 1`,
  i.e., `Nat.choose 4 3 = Nat.choose 4 1`.

  That is the *reverse* of our goal. Use `symm` first to flip the
  goal to `Nat.choose 4 3 = Nat.choose 4 1`.

  Try `symm`."
  Hint (hidden := true) "Try `symm` first, then apply `Nat.choose_symm`."
  symm
  Hint "Good! The goal is now `Nat.choose 4 3 = Nat.choose 4 1`.

  Rewrite `3` as `4 - 1` so that `Nat.choose_symm` matches:

  `rw [show (3 : ℕ) = 4 - 1 from rfl, Nat.choose_symm (by omega : 1 ≤ 4)]`"
  Hint (hidden := true) "Try
  `rw [show (3 : ℕ) = 4 - 1 from rfl, Nat.choose_symm (by omega : 1 ≤ 4)]`."
  rw [show (3 : ℕ) = 4 - 1 from rfl, Nat.choose_symm (by omega : 1 ≤ 4)]

Conclusion
"
You proved $\\binom{4}{1} = \\binom{4}{3}$, confirming the symmetry
of Row 4: **1, 4, 6, 4, 1** reads the same in both directions.

## Why symmetry holds

Combinatorially: choosing 1 element from $\\{a, b, c, d\\}$ (4 ways)
is equivalent to choosing which 3 elements to *keep*. Every 1-element
selection determines a unique 3-element complement, and vice versa.

More generally, $\\binom{n}{k} = \\binom{n}{n-k}$ because choosing
$k$ items to include is the same as choosing $n-k$ items to exclude.

## The full symmetry of Row 4

| Position | $\\binom{4}{k}$ | Symmetric pair | $\\binom{4}{4-k}$ |
|----------|----------------|----------------|------------------|
| $k = 0$ | 1 | $k = 4$ | 1 |
| $k = 1$ | 4 | $k = 3$ | 4 ✓ (just proved) |
| $k = 2$ | 6 | $k = 2$ | 6 (self-paired) |

## What comes next

The final level asks you to step back and confirm the boundary
pattern on a fresh row — a transfer from the computations we
have been doing to a general understanding of the triangle's
structure.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
