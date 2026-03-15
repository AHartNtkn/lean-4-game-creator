import GameServer.Commands
import Mathlib

World "BinomialCoefficients"
Level 6

Title "Symmetry of binomial coefficients"

Introduction
"
# Symmetry: $\\binom{n}{k} = \\binom{n}{n-k}$

One of the most visually striking properties of Pascal's triangle is
its *symmetry*: each row reads the same forwards and backwards.
For example, row 4 is $1, 4, 6, 4, 1$.

Algebraically, this means:

$$\\binom{n}{k} = \\binom{n}{n-k}$$

whenever $k \\le n$.

## The mathlib lemma

```
Nat.choose_symm {n k : ℕ} (h : k ≤ n) : Nat.choose n (n - k) = Nat.choose n k
```

Note the direction: it rewrites `choose n (n - k)` to `choose n k`.
It requires a proof that `k ≤ n`.

## Your task

Prove that $\\binom{7}{5} = \\binom{7}{2}$.

Since $5 = 7 - 2$, this is symmetry with $n = 7, k = 2$.
"

/-- C(7, 5) = C(7, 2) by symmetry. -/
Statement : Nat.choose 7 5 = Nat.choose 7 2 := by
  Hint "You need to use `Nat.choose_symm` to rewrite one side.

  Since `5 = 7 - 2`, the left side `Nat.choose 7 5` can be written as
  `Nat.choose 7 (7 - 2)`, which `Nat.choose_symm` rewrites to
  `Nat.choose 7 2`.

  Try `rw [show (5 : ℕ) = 7 - 2 from rfl, Nat.choose_symm]`."
  Hint (hidden := true) "Try `rw [show (5 : ℕ) = 7 - 2 from rfl, Nat.choose_symm]`.
  You will then need to prove `2 ≤ 7`, which `omega` handles."
  rw [show (5 : ℕ) = 7 - 2 from rfl, Nat.choose_symm]
  Hint "Good! The goal is now `2 ≤ 7`. Use `omega` to close it."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion
"
You proved $\\binom{7}{5} = \\binom{7}{2}$ using the symmetry identity.

## Why symmetry holds

Combinatorially: choosing which 5 elements to *include* from a set of 7
is the same as choosing which 2 elements to *exclude*. Every 5-element
subset corresponds to a unique 2-element complement, and vice versa.

## Using `Nat.choose_symm`

The lemma `Nat.choose_symm` has the form:

$$k \\le n \\implies \\binom{n}{n-k} = \\binom{n}{k}$$

To use it when the goal contains `choose n m` where $m > n/2$, you
often need to first show that $m = n - k$ for some $k$, then apply
the lemma.

## What comes next

The next level explores the combinatorial interpretation of binomial
coefficients — what does $\\binom{n}{k}$ *count*?
"

/-- `Nat.choose_symm` states that if `k ≤ n` then
`Nat.choose n (n - k) = Nat.choose n k`.

This is the symmetry of binomial coefficients: choosing $k$ elements
is the same as choosing which $n - k$ elements to leave out. -/
TheoremDoc Nat.choose_symm as "Nat.choose_symm" in "Nat"

NewTheorem Nat.choose_symm
DisabledTactic trivial decide native_decide simp aesop simp_all
