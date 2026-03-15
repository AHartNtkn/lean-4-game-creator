import GameServer.Commands
import Mathlib

World "BinomialCoefficients"
Level 7

Title "Counting subsets"

Introduction
"
# Counting Subsets: The Combinatorial Interpretation

The binomial coefficient $\\binom{n}{k}$ counts the number of
$k$-element subsets of an $n$-element set. In Lean, this is made
precise using `Finset` and `Fintype`:

The number of $k$-element subsets of `Fin n` is exactly `Nat.choose n k`.

## Transfer moment

On paper, you would say:

> *The number of ways to choose $k$ elements from $\\{0, 1, \\ldots, n-1\\}$
> is $\\binom{n}{k}$.*

In Lean, we express this by counting the finsets of `Fin n` that have
cardinality `k`.

## Your task

Prove that `Nat.choose n 1 = n` — there are exactly $n$ ways to
choose a single element from a set of $n$ elements. This makes
intuitive sense: you can pick any one of the $n$ elements.

## The mathlib lemma

```
Nat.choose_one_right (n : ℕ) : Nat.choose n 1 = n
```
"

/-- There are exactly n ways to choose 1 element from n. -/
Statement (n : ℕ) : Nat.choose n 1 = n := by
  Hint "This is a standard identity. In mathlib, it is
  `Nat.choose_one_right`.

  Try `rw [Nat.choose_one_right]`."
  Hint (hidden := true) "Try `rw [Nat.choose_one_right]` or
  `exact Nat.choose_one_right n`."
  rw [Nat.choose_one_right]

Conclusion
"
You proved $\\binom{n}{1} = n$ — there are exactly $n$ singleton subsets
of an $n$-element set.

## The combinatorial picture

For a set $S = \\{0, 1, \\ldots, n-1\\}$:

| $k$ | $\\binom{n}{k}$ counts | Example ($n = 4$) |
|-----|----------------------|-------------------|
| 0 | empty subsets | $\\{\\}$ — just one |
| 1 | singleton subsets | $\\{0\\}, \\{1\\}, \\{2\\}, \\{3\\}$ — four |
| $n$ | full subsets | $\\{0,1,2,3\\}$ — just one |

## Transfer

On paper: *\"There are $n$ ways to choose 1 element from $n$ because
each element gives a distinct singleton subset.\"*

In Lean: `Nat.choose_one_right n : Nat.choose n 1 = n`.

The Lean proof does not reason combinatorially — it uses the
recursive definition. But the statement captures the combinatorial fact.

## What comes next

The next level proves a beautiful identity: the sum of an entire row
of Pascal's triangle equals a power of 2.
"

/-- `Nat.choose_one_right` states that `Nat.choose n 1 = n`.

There are exactly `n` ways to choose a single element from a set
of `n` elements. -/
TheoremDoc Nat.choose_one_right as "Nat.choose_one_right" in "Nat"

NewTheorem Nat.choose_one_right
DisabledTactic trivial decide native_decide simp aesop simp_all
