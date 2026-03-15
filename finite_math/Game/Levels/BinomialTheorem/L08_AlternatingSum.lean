import GameServer.Commands
import Mathlib

World "BinomialTheorem"
Level 8

Title "Alternating sum of binomial coefficients"

Introduction
"
# Alternating Sum: $\\sum (-1)^k \\binom{n}{k} = 0$

Setting $x = 1, y = -1$ in the binomial theorem gives a beautiful
identity. For $n \\ge 1$:

$$(1 + (-1))^n = \\sum_{k=0}^{n} (-1)^k \\cdot \\binom{n}{k} = 0^n = 0$$

So the alternating sum of binomial coefficients vanishes:

$$\\binom{n}{0} - \\binom{n}{1} + \\binom{n}{2} - \\binom{n}{3} + \\cdots = 0$$

For $n = 4$: $1 - 4 + 6 - 4 + 1 = 0$. ✓

## In Lean

This identity lives in `ℤ` (because of the $(-1)^k$ factor). The
mathlib lemma is:

```
Int.alternating_sum_range_choose_of_ne {n : ℕ} (hn : n ≠ 0) :
  ∑ m ∈ Finset.range (n + 1), (-1) ^ m * ↑(Nat.choose n m) = 0
```

## Your task

Prove the alternating sum identity for a general `n ≥ 1`.
"

/-- The alternating sum of binomial coefficients is zero for n ≥ 1. -/
Statement (n : ℕ) (hn : n ≠ 0) :
    ∑ m ∈ Finset.range (n + 1), (-1 : ℤ) ^ m * ↑(Nat.choose n m) = 0 := by
  Hint "The library lemma `Int.alternating_sum_range_choose_of_ne` states
  exactly this, given a proof that `n ≠ 0`.

  Try `exact Int.alternating_sum_range_choose_of_ne hn`."
  Hint (hidden := true) "Try `exact Int.alternating_sum_range_choose_of_ne hn`."
  exact Int.alternating_sum_range_choose_of_ne hn

Conclusion
"
## Why the alternating sum is zero

**Algebraic proof** (from the binomial theorem):

Set $x = 1, y = -1$ in $(x + y)^n$. For $n \\ge 1$:

$$(1 + (-1))^n = 0^n = 0 = \\sum_{k=0}^{n} 1^k \\cdot (-1)^{n-k} \\cdot \\binom{n}{k}$$

Since $1^k = 1$ and $(-1)^{n-k} = (-1)^n \\cdot (-1)^{-k}$... the
exact manipulation is a bit fiddly, but the key idea is clear:
substituting $y = -1$ makes alternating signs appear.

**Combinatorial proof**:

The even-sized subsets and odd-sized subsets of a nonempty set pair up.
For each element $x$ in the set, the map $S \\mapsto S \\triangle \\{x\\}$
(symmetric difference with $\\{x\\}$) is a bijection between even-sized
and odd-sized subsets. So $\\sum_{\\text{even}} \\binom{n}{k} = \\sum_{\\text{odd}} \\binom{n}{k}$,
which means the alternating sum is zero.

## Transfer

On paper: *\"Set $y = -1$ in the binomial theorem to get
$0 = 0^n = \\sum (-1)^k \\binom{n}{k}$ for $n \\ge 1$.\"*

## What comes next

The next level is a **transfer** level: stating the binomial theorem
in ordinary mathematical notation.
"

/-- `Int.alternating_sum_range_choose_of_ne` states that for `n ≠ 0`,
`∑ m ∈ Finset.range (n + 1), (-1) ^ m * ↑(Nat.choose n m) = 0`.

This is the alternating sum identity for binomial coefficients: the
even-position coefficients and odd-position coefficients sum to the
same value. -/
TheoremDoc Int.alternating_sum_range_choose_of_ne as "Int.alternating_sum_range_choose_of_ne" in "Int"

NewTheorem Int.alternating_sum_range_choose_of_ne
DisabledTactic trivial decide native_decide simp aesop simp_all
