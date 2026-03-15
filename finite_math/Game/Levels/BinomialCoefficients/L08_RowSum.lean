import GameServer.Commands
import Mathlib

World "BinomialCoefficients"
Level 8

Title "Row sum equals 2^n"

Introduction
"
# Row Sum: $\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$

One of the most elegant identities in combinatorics: the sum of
all entries in row $n$ of Pascal's triangle equals $2^n$.

$$\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$$

## Why?

Combinatorially: every subset of an $n$-element set either has 0
elements, or 1 element, or 2 elements, ..., or $n$ elements. The
total number of subsets is $2^n$ (each element is independently
in or out). So:

$$\\binom{n}{0} + \\binom{n}{1} + \\cdots + \\binom{n}{n} = 2^n$$

## Concrete example

For $n = 3$: $1 + 3 + 3 + 1 = 8 = 2^3$. ✓

## Your task

First, verify the identity for $n = 4$ using the mathlib lemma:

```
Nat.sum_range_choose (n : ℕ) :
  ∑ m ∈ Finset.range (n + 1), Nat.choose n m = 2 ^ n
```

This is a direct application — use `exact` or `rw`.
"

/-- The row sum identity for n = 4. -/
Statement : ∑ m ∈ Finset.range 5, Nat.choose 4 m = 2 ^ 4 := by
  Hint "This is a direct instance of `Nat.sum_range_choose` with `n = 4`.

  Note that `Finset.range 5 = Finset.range (4 + 1)`, so the lemma
  applies directly.

  Try `exact Nat.sum_range_choose 4`."
  Hint (hidden := true) "Try `exact Nat.sum_range_choose 4`."
  exact Nat.sum_range_choose 4

Conclusion
"
You verified the row sum identity:

$$\\sum_{k=0}^{4} \\binom{4}{k} = 1 + 4 + 6 + 4 + 1 = 16 = 2^4$$

## The general identity

`Nat.sum_range_choose n` states:

$$\\sum_{m=0}^{n} \\binom{n}{m} = 2^n$$

This identity has several proofs:
- **Combinatorial**: count subsets by size vs. by inclusion/exclusion
- **Algebraic**: set $x = 1$ in $(1+x)^n = \\sum_k \\binom{n}{k} x^k$
- **Inductive**: use Pascal's rule to relate row $n+1$ to row $n$

## Transfer

On paper: *\"The number of subsets of an $n$-element set is $2^n$.
Partitioning subsets by cardinality gives
$\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$.\"*

This is one of the fundamental counting identities that connects
binomial coefficients to powers of 2.

## What comes next

The boss level puts everything together.
"

/-- `Nat.sum_range_choose` states that
`∑ m ∈ Finset.range (n + 1), Nat.choose n m = 2 ^ n`.

The sum of all binomial coefficients in row $n$ of Pascal's triangle
equals $2^n$. This follows from counting all subsets of an $n$-element
set by size. -/
TheoremDoc Nat.sum_range_choose as "Nat.sum_range_choose" in "Nat"

NewTheorem Nat.sum_range_choose
DisabledTactic trivial decide native_decide simp aesop simp_all
