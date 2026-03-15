import GameServer.Commands
import Mathlib

World "Capstone"
Level 5

Title "Powerset cardinality meets binomial coefficients"

Introduction
"
# Powerset cardinality = sum of binomial coefficients

One of the most elegant connections in combinatorics: the number of
subsets of an $n$-element set equals $2^n$, which also equals the sum
of all binomial coefficients $\\sum_{k=0}^{n} \\binom{n}{k}$.

## The two sides

**Left side** (from the **FinsetCardinality** world):
```
card (powerset s) = 2 ^ card s     -- Finset.card_powerset
card (range n) = n                   -- Finset.card_range
```

**Right side** (from the **BinomialCoefficients** / **BinomialTheorem** worlds):
```
∑ k in range (n+1), Nat.choose n k = 2 ^ n     -- Nat.sum_range_choose
```

Since both sides equal $2^n$, they are equal to each other.

## Your task

Prove that `(Finset.range 4).powerset.card = ∑ k ∈ Finset.range 5, Nat.choose 4 k`.

This connects the **finset** module with the **binomial coefficient** module.
"

/-- The number of subsets of a 4-element set equals the sum of `C(4,k)` for `k = 0..4`. -/
Statement : (Finset.range 4).powerset.card = ∑ k ∈ Finset.range 5, Nat.choose 4 k := by
  Hint "**Step 1**: Simplify the left side.

  Use `rw [Finset.card_powerset, Finset.card_range]` to get
  `2 ^ 4 = ∑ ...`."
  Hint (hidden := true) "Try `rw [Finset.card_powerset, Finset.card_range]`."
  rw [Finset.card_powerset, Finset.card_range]
  Hint "**Step 2**: Simplify the right side.

  Use `rw [Nat.sum_range_choose]` to collapse the sum of binomial
  coefficients to `2 ^ 4`."
  Hint (hidden := true) "Try `rw [Nat.sum_range_choose]`."
  rw [Nat.sum_range_choose]

Conclusion
"
You proved a fundamental combinatorial identity by connecting two
different parts of the course:

- **Finset.card_powerset**: $|\\mathcal{P}(S)| = 2^{|S|}$
- **Nat.sum_range_choose**: $\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$

Both reduce to $2^n$, proving they are equal.

## In ordinary mathematics

> *The number of subsets of $\\{0, 1, 2, 3\\}$ is $2^4 = 16$. By the
> binomial coefficient row-sum identity, $\\sum_{k=0}^{4} \\binom{4}{k} = 2^4 = 16$.
> Therefore the two quantities are equal.* $\\square$

## Why this matters

This connects two views of the same fact:
- **Set-theoretic**: count subsets directly via the powerset.
- **Algebraic**: sum binomial coefficients (counting subsets by size).

The binomial theorem (setting $x = y = 1$ in $(x+y)^n$) gives the
algebraic proof; the powerset gives the combinatorial proof.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
