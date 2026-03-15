import GameServer.Commands
import Mathlib

World "FinsetProd"
Level 5

Title "Distributing addition inside a sum"

Introduction
"
# `Finset.sum_add_distrib`: splitting a sum of sums

In ordinary algebra, you freely rearrange
$$\\sum_{i=0}^{n-1} (f(i) + g(i)) = \\sum_{i=0}^{n-1} f(i) + \\sum_{i=0}^{n-1} g(i).$$

In Lean, this is the lemma `Finset.sum_add_distrib`:

```
Finset.sum_add_distrib :
  ∑ x ∈ s, (f x + g x) = (∑ x ∈ s, f x) + (∑ x ∈ s, g x)
```

This says: a sum of pointwise sums splits into a sum of each part.

## Your task

Prove:
$$\\sum_{i \\in \\mathrm{range}\\, n} (2i + 3) = \\left(\\sum_{i \\in \\mathrm{range}\\, n} 2i\\right) + \\left(\\sum_{i \\in \\mathrm{range}\\, n} 3\\right)$$

Use `rw [Finset.sum_add_distrib]`.
"

/-- Distributing addition inside a sum. -/
Statement (n : Nat) :
    ∑ i ∈ Finset.range n, (2 * i + 3) =
    (∑ i ∈ Finset.range n, 2 * i) + (∑ i ∈ Finset.range n, 3) := by
  Hint "Use `Finset.sum_add_distrib` to split the sum of a pointwise
  sum into the sum of each component.

  Try `rw [Finset.sum_add_distrib]`."
  Hint (hidden := true) "Try `rw [Finset.sum_add_distrib]`."
  rw [Finset.sum_add_distrib]

Conclusion
"
You split `∑ (f + g)` into `∑ f + ∑ g` using `sum_add_distrib`.

## Why this matters

This lemma is the foundation of algebraic manipulation inside
big-operator goals. When you have a sum of a complicated expression,
`sum_add_distrib` lets you break it into simpler pieces that you can
handle separately.

## The multiplicative analogue

The multiplicative version is `Finset.prod_mul_distrib`:

```
∏ x ∈ s, (f x * g x) = (∏ x ∈ s, f x) * (∏ x ∈ s, g x)
```

A product of pointwise products splits into a product of each part.

## What comes next

The next level covers pulling a constant factor out of a sum.
"

/-- `Finset.sum_add_distrib` states that
`∑ x ∈ s, (f x + g x) = (∑ x ∈ s, f x) + (∑ x ∈ s, g x)`.

A sum of pointwise sums splits into the sum of each part. -/
TheoremDoc Finset.sum_add_distrib as "Finset.sum_add_distrib" in "Finset"

/-- `Finset.prod_mul_distrib` states that
`∏ x ∈ s, (f x * g x) = (∏ x ∈ s, f x) * (∏ x ∈ s, g x)`.

A product of pointwise products splits into the product of each part. -/
TheoremDoc Finset.prod_mul_distrib as "Finset.prod_mul_distrib" in "Finset"

NewTheorem Finset.sum_add_distrib Finset.prod_mul_distrib
DisabledTactic trivial decide native_decide simp aesop simp_all
