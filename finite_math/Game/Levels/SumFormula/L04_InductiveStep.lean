import GameServer.Commands
import Mathlib

World "SumFormula"
Level 4

Title "Prove the inductive step"

Introduction
"
# The inductive step

Now for the heart of the proof. You are given:

- `n : Nat`
- `ih : 2 * (∑ i ∈ Finset.range (n + 1), i) = (n + 1) * n`

and must prove:

`2 * (∑ i ∈ Finset.range (n + 1 + 1), i) = (n + 1 + 1) * (n + 1)`

## Strategy

1. **Peel off the last term**: `rw [Finset.sum_range_succ]` rewrites the
   sum as `(∑ i ∈ range (n+1), i) + (n+1)`.

2. **Distribute the 2**: `rw [Nat.mul_add]` turns
   `2 * (sum + (n+1))` into `2 * sum + 2 * (n+1)`.

3. **Apply the inductive hypothesis**: `rw [ih]` replaces `2 * sum`
   with `(n+1) * n`.

4. **Close the algebra**: `ring` verifies
   $(n+1) \\cdot n + 2 \\cdot (n+1) = (n+2) \\cdot (n+1)$.

You can do steps 1-3 in a single rewrite: `rw [Finset.sum_range_succ,
Nat.mul_add, ih]`, then `ring`.
"

/-- The inductive step of Gauss's formula. -/
Statement (n : Nat) (ih : 2 * (∑ i ∈ Finset.range (n + 1), i) = (n + 1) * n) :
    2 * (∑ i ∈ Finset.range (n + 1 + 1), i) = (n + 1 + 1) * (n + 1) := by
  Hint "Start by peeling off the last term:
  `rw [Finset.sum_range_succ]`.

  This rewrites the sum as `(∑ i ∈ range (n+1), i) + (n+1)`."
  rw [Finset.sum_range_succ]
  Hint "Now distribute the `2` across the addition:
  `rw [Nat.mul_add]`.

  This turns `2 * (sum + (n+1))` into `2 * sum + 2 * (n+1)`."
  rw [Nat.mul_add]
  Hint "Apply the inductive hypothesis: `rw [ih]`.

  This replaces `2 * (∑ i ∈ range (n+1), i)` with `(n+1) * n`."
  rw [ih]
  Hint "The goal is now:
  `(n + 1) * n + 2 * (n + 1) = (n + 1 + 1) * (n + 1)`

  This is a polynomial equality: $(n+1)n + 2(n+1) = (n+2)(n+1)$.
  Factor out $(n+1)$: $(n+1)(n + 2) = (n+2)(n+1)$.

  Use `ring` to close it."
  Hint (hidden := true) "Use `ring`."
  ring

Conclusion
"
You proved the inductive step!

## The algebra

The key identity is:
$$(n+1) \\cdot n + 2 \\cdot (n+1) = (n+1)(n+2) = (n+2)(n+1)$$

This works because we can factor out $(n+1)$:
$$(n+1) \\cdot n + 2 \\cdot (n+1) = (n+1)(n + 2)$$

The `ring` tactic verifies this automatically.

## Why no subtraction issues?

Notice that our formula uses $(n+1) \\cdot n$ rather than
$n \\cdot (n-1)$. This avoids natural-number subtraction entirely, so
`ring` works perfectly. If we had used $n \\cdot (n-1)$, we would need
extra work to handle the case $n = 0$ where $n - 1$ truncates to $0$
in the natural numbers.

## Next up

Now you will combine the base case and inductive step into a single
complete proof.
"

/-- `Nat.mul_add a b c` states that `a * (b + c) = a * b + a * c`.

This is left-distributivity of multiplication over addition for
natural numbers. Use `rw [Nat.mul_add]` to distribute a factor
across a sum. -/
TheoremDoc Nat.mul_add as "Nat.mul_add" in "Nat"

NewTheorem Nat.mul_add
DisabledTactic trivial decide native_decide simp aesop simp_all
