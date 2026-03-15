import GameServer.Commands
import Mathlib

World "FinsetProd"
Level 3

Title "prod_range_succ"

Introduction
"
# Peeling off the last factor

You learned `sum_range_succ` in the Range Sum Induction world:

```
∑ x ∈ range (n + 1), f x = (∑ x ∈ range n, f x) + f n
```

The multiplicative analogue is `Finset.prod_range_succ`:

```
Finset.prod_range_succ (f : ℕ → M) (n : ℕ) :
  ∏ x ∈ range (n + 1), f x = (∏ x ∈ range n, f x) * f n
```

It says: to compute the product over `range (n+1)`, take the product
over `range n` and multiply by `f n`.

## Your task

Use `prod_range_succ` to prove a concrete instance:

$$\\prod_{i=0}^{3} (i + 1) = \\left(\\prod_{i=0}^{2} (i + 1)\\right) \\cdot 4$$

In Lean: `∏ i ∈ range 4, (i + 1) = (∏ i ∈ range 3, (i + 1)) * 4`.
"

/-- Peel off the last factor of a concrete range product. -/
Statement : ∏ i ∈ Finset.range 4, (i + 1) = (∏ i ∈ Finset.range 3, (i + 1)) * 4 := by
  Hint "Apply the peeling-off lemma: `rw [Finset.prod_range_succ]`.
  Since `range 4 = range (3 + 1)`, this rewrites the left-hand side to
  `(∏ i ∈ range 3, (i + 1)) * (3 + 1)`."
  Hint (hidden := true) "Try `rw [Finset.prod_range_succ]`."
  rw [Finset.prod_range_succ]

Conclusion
"
You used `prod_range_succ` to split off the last factor from a
range product.

## The pattern

Just like `sum_range_succ` for sums, `prod_range_succ` is the key
lemma for inductive proofs about products. The inductive step will
always begin with:

```
rw [Finset.prod_range_succ]
```

This converts `∏ i ∈ range (n + 1), f i` into
`(∏ i ∈ range n, f i) * f n`, and then you can apply the inductive
hypothesis to the product over `range n`.

## What comes next

Now that you have the basic product API, the next level introduces
`ring` for algebraic manipulation — a tactic that will be essential
for working with sums and products together.
"

/-- `Finset.prod_range_succ` states that
`∏ x ∈ range (n + 1), f x = (∏ x ∈ range n, f x) * f n`.

This decomposes a product over `range (n+1)` by peeling off the last
factor `f n`. -/
TheoremDoc Finset.prod_range_succ as "Finset.prod_range_succ" in "Finset"

NewTheorem Finset.prod_range_succ
DisabledTactic trivial decide native_decide simp aesop simp_all
