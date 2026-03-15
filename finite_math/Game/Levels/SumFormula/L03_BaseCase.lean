import GameServer.Commands
import Mathlib

World "SumFormula"
Level 3

Title "Prove the base case"

Introduction
"
# Base case of the induction

The full statement we want to prove is:

$$\\forall\\, n,\\quad 2 \\cdot \\sum_{i=0}^{n} i \\;=\\; (n+1) \\cdot n$$

In Lean: `∀ n, 2 * (∑ i ∈ Finset.range (n + 1), i) = (n + 1) * n`.

The proof is by induction on $n$. In this level, you prove just the
**base case**: when $n = 0$, the formula says
$2 \\cdot \\sum_{i \\in \\text{range } 1} i = 1 \\cdot 0$.

Since `range 1 = {0}` and the sum of `{0}` is `0`, both sides equal `0`.

## Your task

Prove: `2 * (∑ i ∈ Finset.range 1, i) = 1 * 0`.

This is definitionally true, so `rfl` suffices.
"

/-- Base case: `2 * (∑ i ∈ range 1, i) = 1 * 0`. -/
Statement : 2 * (∑ i ∈ Finset.range 1, i) = 1 * 0 := by
  Hint "Both sides reduce to `0`. Try `rfl`."
  Hint (hidden := true) "Use `rfl`."
  rfl

Conclusion
"
The base case is trivial: both sides are `0`.

## Why is this so easy?

When $n = 0$:
- The left side is $2 \\cdot \\sum_{i \\in \\text{range } 1} i = 2 \\cdot 0 = 0$.
  (The only element of `range 1` is `0`, and the identity function maps
  it to `0`.)
- The right side is $(0 + 1) \\cdot 0 = 0$.

Lean can verify `0 = 0` by definitional computation, which is exactly
what `rfl` does.

## Next up

The interesting part is the **inductive step**: assuming the formula for
$n$, prove it for $n + 1$.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
