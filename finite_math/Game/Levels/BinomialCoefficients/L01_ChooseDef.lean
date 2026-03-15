import GameServer.Commands
import Mathlib

World "BinomialCoefficients"
Level 1

Title "What is C(n, k)?"

Introduction
"
# Binomial Coefficients

Welcome to the **Binomial Coefficients** world! The binomial
coefficient $\\binom{n}{k}$, also written $C(n,k)$, counts the number
of ways to choose $k$ elements from a set of $n$ elements. It appears
throughout combinatorics, algebra, and probability.

## Definition

In Lean, the binomial coefficient is `Nat.choose n k`. It is defined
recursively using Pascal's rule:

$$\\binom{n+1}{k+1} = \\binom{n}{k} + \\binom{n}{k+1}$$

with boundary conditions $\\binom{n}{0} = 1$ and $\\binom{0}{k+1} = 0$.

## Key lemmas

The boundary lemmas you will use:
```
Nat.choose_zero_right (n : ℕ) : Nat.choose n 0 = 1
Nat.choose_zero_succ (k : ℕ) : Nat.choose 0 (k + 1) = 0
Nat.choose_succ_succ (n k : ℕ) : Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1)
```

## Your task

Compute $\\binom{4}{2} = 6$ by repeatedly applying these three
lemmas to unfold the recursion. This is the same recursive
computation you would do by hand on Pascal's triangle.
"

/-- Compute C(4,2) = 6 by unfolding the recursive definition. -/
Statement : Nat.choose 4 2 = 6 := by
  Hint "Apply `Nat.choose_succ_succ` to unfold the recursion. Each
  application rewrites `choose (n+1) (k+1)` as `choose n k + choose n (k+1)`.

  Try `rw [Nat.choose_succ_succ]` — Lean will match `4` as `3 + 1` and
  `2` as `1 + 1`, rewriting to `Nat.choose 3 1 + Nat.choose 3 2 = 6`."
  Hint (hidden := true) "Apply `rw [Nat.choose_succ_succ]` repeatedly.
  Each step splits a binomial coefficient into two smaller ones.
  When a term has `k = 0`, use `Nat.choose_zero_right`.
  When `choose n n` appears, use `Nat.choose_self`."
  rw [Nat.choose_succ_succ]
  Hint "Good! Now you have `Nat.choose 3 1 + Nat.choose 3 2 = 6`.
  Keep applying `Nat.choose_succ_succ` to break these down further."
  rw [Nat.choose_succ_succ]
  Hint "Now `Nat.choose_zero_right` can simplify a term where `k = 0`.
  Try `rw [Nat.choose_zero_right]`."
  rw [Nat.choose_zero_right]
  Hint "Keep going — apply `Nat.choose_succ_succ` again to continue
  breaking down the remaining binomial coefficients."
  rw [Nat.choose_succ_succ]
  rw [Nat.choose_zero_right]
  rw [Nat.choose_self]
  Hint "Continue unfolding the remaining terms. Use `Nat.choose_succ_succ`
  for recursive cases and `Nat.choose_self`, `Nat.choose_zero_right`
  for base cases."
  rw [Nat.choose_succ_succ]
  rw [Nat.choose_succ_succ]
  rw [Nat.choose_zero_right]
  rw [Nat.choose_self]
  rw [Nat.choose_self]

Conclusion
"
You computed $\\binom{4}{2} = 6$ by systematically unfolding the
recursive definition.

The computation traced through Pascal's triangle:

$$\\binom{4}{2} = \\binom{3}{1} + \\binom{3}{2} = (1 + 2) + (2 + 1) = 6$$

## The three key lemmas

- `Nat.choose_succ_succ`: the recursive case — $\\binom{n+1}{k+1} = \\binom{n}{k} + \\binom{n}{k+1}$
- `Nat.choose_zero_right`: the base case — $\\binom{n}{0} = 1$
- `Nat.choose_zero_succ`: the other boundary — $\\binom{0}{k+1} = 0$

## What comes next

The next level explores the boundary values more carefully,
introducing `Nat.choose_self`: $\\binom{n}{n} = 1$.
"

/-- `Nat.choose n k` is the binomial coefficient $\\binom{n}{k}$,
the number of ways to choose `k` elements from `n`.

It is defined recursively by Pascal's rule with boundary conditions. -/
DefinitionDoc Nat.choose as "Nat.choose"

/-- `Nat.choose_zero_right` states that `Nat.choose n 0 = 1` for all `n`.

Choosing zero elements from any set can be done in exactly one way:
take the empty subset. -/
TheoremDoc Nat.choose_zero_right as "Nat.choose_zero_right" in "Nat"

/-- `Nat.choose_zero_succ` states that `Nat.choose 0 (k + 1) = 0`.

You cannot choose any positive number of elements from an empty set. -/
TheoremDoc Nat.choose_zero_succ as "Nat.choose_zero_succ" in "Nat"

/-- `Nat.choose_succ_succ` states that
`Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1)`.

This is Pascal's rule: each entry in Pascal's triangle is the sum of the
two entries above it. -/
TheoremDoc Nat.choose_succ_succ as "Nat.choose_succ_succ" in "Nat"

NewTheorem Nat.choose_zero_right Nat.choose_zero_succ Nat.choose_succ_succ
NewDefinition Nat.choose
DisabledTactic trivial decide native_decide simp aesop simp_all
