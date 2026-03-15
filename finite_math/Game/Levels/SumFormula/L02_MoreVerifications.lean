import GameServer.Commands
import Mathlib

World "SumFormula"
Level 2

Title "More concrete checks"

Introduction
"
# Checking the formula for small values

Before diving into the general proof, let us verify the formula for one
more value. This time, verify it for $n = 2$: $2 \\cdot (0 + 1 + 2) = 3
\\cdot 2$.

You can use `norm_num` with the sum-unfolding lemmas, or you can unfold
manually with `rw [Finset.sum_range_succ]` repeated three times, followed
by `rw [Finset.sum_range_zero]`, and then `rfl`.

## Manual unfolding

If you want to see each step:
1. `rw [Finset.sum_range_succ]` — peels off the $i = 2$ term
2. `rw [Finset.sum_range_succ]` — peels off the $i = 1$ term
3. `rw [Finset.sum_range_succ]` — peels off the $i = 0$ term
4. `rw [Finset.sum_range_zero]` — the empty sum is $0$
5. `rfl` or `norm_num` — both sides are now numerals
"

/-- Verify Gauss's formula for n = 2: `2 * (0 + 1 + 2) = 3 * 2`. -/
Statement : 2 * (∑ i ∈ Finset.range 3, i) = 3 * 2 := by
  Hint "You can use `norm_num [Finset.sum_range_succ, Finset.sum_range_zero]`
  to compute everything at once.

  Or unfold step by step:
  `rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
       Finset.sum_range_zero]`
  then `rfl`."
  Hint (hidden := true) "Try `norm_num [Finset.sum_range_succ, Finset.sum_range_zero]`."
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

Conclusion
"
You verified that $2 \\cdot (0 + 1 + 2) = 6 = 3 \\cdot 2$.

## Checking vs. proving

Concrete verification is reassuring, but each check only confirms one
value of $n$. In the next levels, you will prove the formula for
**all** $n$ at once, using induction.

## The plan for the inductive proof

1. **Base case** ($n = 0$): The sum $\\sum_{i \\in \\text{range } 1} i = 0$,
   and $(0 + 1) \\cdot 0 = 0$.
2. **Inductive step**: Assume the formula holds for $n$. Prove it for
   $n + 1$ by peeling off the last term with `sum_range_succ` and using
   algebra.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
