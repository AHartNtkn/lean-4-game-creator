import GameServer.Commands
import Mathlib

World "RangeSumInduction"
Level 2

Title "sum_range_succ"

Introduction
"
# The peeling-off lemma

The most important lemma in this world is `Finset.sum_range_succ`:

```
Finset.sum_range_succ (f : Nat → M) (n : Nat) :
  ∑ x ∈ Finset.range (n + 1), f x = (∑ x ∈ Finset.range n, f x) + f n
```

It says: to compute the sum over `range (n+1)`, take the sum over
`range n` and add `f n` (the last term).

This is the analogue of `sum_cons` and `sum_insert` but specialized to
ranges. It will be our main tool for inductive proofs.

## Your task

Use `sum_range_succ` to prove a concrete instance:

$$\\sum_{i=0}^{3} i = \\left(\\sum_{i=0}^{2} i\\right) + 3$$

In Lean: `∑ i ∈ range 4, i = (∑ i ∈ range 3, i) + 3`.
"

/-- Peel off the last term of a concrete range sum. -/
Statement : ∑ i ∈ Finset.range 4, i = (∑ i ∈ Finset.range 3, i) + 3 := by
  Hint "Apply the peeling-off lemma: `rw [Finset.sum_range_succ]`.
  Since `range 4 = range (3 + 1)`, this rewrites the left-hand side to
  `(∑ i ∈ range 3, i) + 3`."
  Hint (hidden := true) "Try `rw [Finset.sum_range_succ]`."
  rw [Finset.sum_range_succ]

Conclusion
"
You used `sum_range_succ` to split off the last term of a range sum.

## The pattern

In an inductive proof about `∑ i ∈ range n, f i`, the inductive step
will always begin with:

```
rw [Finset.sum_range_succ]
```

This converts `∑ i ∈ range (n + 1), f i` into
`(∑ i ∈ range n, f i) + f n`, and then you can apply the inductive
hypothesis to the sum over `range n`.

## What comes next

Now that you have this lemma, you are ready for your first *inductive*
sum proof.
"

/-- `Finset.sum_range_succ` states that
`∑ x ∈ Finset.range (n + 1), f x = (∑ x ∈ Finset.range n, f x) + f n`.

This decomposes a sum over `range (n+1)` by peeling off the last term `f n`. -/
TheoremDoc Finset.sum_range_succ as "Finset.sum_range_succ" in "Finset"

NewTheorem Finset.sum_range_succ
DisabledTactic trivial decide native_decide simp aesop simp_all
