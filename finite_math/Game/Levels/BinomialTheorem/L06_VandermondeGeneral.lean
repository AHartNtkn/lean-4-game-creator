import GameServer.Commands
import Mathlib

World "BinomialTheorem"
Level 6

Title "Vandermonde's identity"

Introduction
"
# Vandermonde's Identity (Convolution)

Vandermonde's identity is one of the great identities in combinatorics:

$$\\binom{m + n}{k} = \\sum_{j=0}^{k} \\binom{m}{j} \\cdot \\binom{n}{k - j}$$

It says that the number of ways to choose $k$ elements from a set of
$m + n$ elements equals the total over all ways to split the selection:
choose $j$ from the first $m$ elements and $k - j$ from the last $n$.

## In Lean

The mathlib lemma `Nat.add_choose_eq` states this using `Finset.antidiagonal`:

```
Nat.add_choose_eq (m n k : ℕ) :
  Nat.choose (m + n) k =
    ∑ ij ∈ Finset.antidiagonal k,
      Nat.choose m ij.1 * Nat.choose n ij.2
```

Here `Finset.antidiagonal k` is the set of all pairs `(i, j)` with
`i + j = k`. So `ij.1` plays the role of $j$ and `ij.2 = k - j$.

## Your task

Apply Vandermonde's identity in general form.
"

/-- Vandermonde's identity in general form. -/
Statement (m n k : ℕ) :
    Nat.choose (m + n) k =
      ∑ ij ∈ Finset.antidiagonal k, Nat.choose m ij.1 * Nat.choose n ij.2 := by
  Hint "This is `Nat.add_choose_eq` applied directly.

  Try `exact Nat.add_choose_eq m n k`."
  Hint (hidden := true) "Try `exact Nat.add_choose_eq m n k`."
  exact Nat.add_choose_eq m n k

Conclusion
"
You stated and applied Vandermonde's identity!

## Combinatorial meaning

Consider a group of $m$ men and $n$ women. To form a committee of $k$
people, you can choose $j$ men and $k - j$ women for each valid $j$.
The total is:

$$\\binom{m+n}{k} = \\sum_{j=0}^{k} \\binom{m}{j} \\cdot \\binom{n}{k-j}$$

## About `Finset.antidiagonal`

The set `Finset.antidiagonal k` contains all pairs `(i, j)` of natural
numbers with `i + j = k`:

- `antidiagonal 0 = {(0, 0)}`
- `antidiagonal 1 = {(0, 1), (1, 0)}`
- `antidiagonal 2 = {(0, 2), (1, 1), (2, 0)}`

This is a convenient way to express \"sum over all splits of $k$\"
without explicitly writing the bounds.

## What comes next

The next level applies Vandermonde's identity to a concrete numerical
example.
"

/-- `Nat.add_choose_eq` is Vandermonde's identity:
`Nat.choose (m + n) k = ∑ ij ∈ Finset.antidiagonal k, Nat.choose m ij.1 * Nat.choose n ij.2`.

The number of ways to choose `k` elements from `m + n` equals the sum
over all ways to split: choose `j` from the first `m` and `k - j` from
the last `n`. -/
TheoremDoc Nat.add_choose_eq as "Nat.add_choose_eq" in "Nat"

/-- `Finset.antidiagonal k` is the finset of all pairs `(i, j)` of natural
numbers with `i + j = k`. It provides a clean way to sum over all ways
to split `k` into two parts. -/
DefinitionDoc Finset.antidiagonal as "Finset.antidiagonal"

NewTheorem Nat.add_choose_eq
NewDefinition Finset.antidiagonal
DisabledTactic trivial decide native_decide simp aesop simp_all
