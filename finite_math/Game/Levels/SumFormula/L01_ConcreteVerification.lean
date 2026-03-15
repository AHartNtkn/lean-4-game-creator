import GameServer.Commands
import Mathlib

World "SumFormula"
Level 1

Title "Compute the sum for small n"

Introduction
"
# The sum of the first n natural numbers

Welcome to the **Sum Formula** world! In this world you will prove the
classic formula attributed to young Gauss:

$$0 + 1 + 2 + \\cdots + n = \\frac{n(n+1)}{2}$$

To avoid natural-number division, we state this as:

$$2 \\cdot \\sum_{i=0}^{n} i \\;=\\; (n+1) \\cdot n$$

## Concrete verification

Before proving the formula in general, let us check it for a specific
value. Verify that $2 \\cdot (0 + 1 + 2 + 3 + 4) = 5 \\cdot 4$.

## Strategy

Use `norm_num [Finset.sum_range_succ, Finset.sum_range_zero]` to unfold
the sum and compute both sides. The `norm_num` tactic handles the
arithmetic once the sum has been expanded.
"

/-- Verify Gauss's formula for n = 4: `2 * (0 + 1 + 2 + 3 + 4) = 5 * 4`. -/
Statement : 2 * (∑ i ∈ Finset.range 5, i) = 5 * 4 := by
  Hint "Use `norm_num [Finset.sum_range_succ, Finset.sum_range_zero]` to
  unfold the sum and verify the arithmetic."
  Hint (hidden := true) "Try `norm_num [Finset.sum_range_succ, Finset.sum_range_zero]`."
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

Conclusion
"
You verified that $2 \\cdot (0 + 1 + 2 + 3 + 4) = 20 = 5 \\cdot 4$.

## What happened

The `norm_num` tactic, given the lemmas `sum_range_succ` and
`sum_range_zero`, expanded:
$$\\sum_{i \\in \\text{range } 5} i
  = \\Big(\\sum_{i \\in \\text{range } 4} i\\Big) + 4
  = \\cdots = 0 + 0 + 1 + 2 + 3 + 4 = 10$$
and then checked $2 \\cdot 10 = 20 = 5 \\cdot 4$.

## The pattern

For any specific $n$, we can compute and check. But of course we want
a proof that works for **all** $n$. That is what the rest of this world
is about.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
