import GameServer.Commands
import Mathlib

World "BigOpPset"
Level 1

Title "Fresh inductive sum"

Introduction
"
# Big-Operator Fluency: Problem Set

Welcome to the big-operator problem set. In this world you will
retrieve skills from the big-operator worlds (W13–W16) under
**reduced scaffolding**: fewer hints, fresh surface forms, and
minimal guidance.

## Level 1: A fresh inductive sum

Prove by induction:

$$\\sum_{i=0}^{n-1} 2 \\;=\\; 2n$$

This is the sum of `n` twos. The proof follows the same
three-step pattern you learned in the Range Sum Induction world:
induction → peel off the last term → apply the hypothesis.

The difference from `∑ i ∈ range n, 1 = n` is purely cosmetic:
the constant is `2` instead of `1`.
"

/-- The sum of `n` twos is `2 * n`. -/
Statement (n : Nat) : ∑ i ∈ Finset.range n, 2 = 2 * n := by
  Hint (hidden := true) "Start with `induction n with` to set up the
  base case and inductive step."
  induction n with
  | zero =>
    Hint (hidden := true) "The base case: `∑ i ∈ range 0, 2 = 2 * 0`.
    Both sides reduce to `0`. Use `rfl`."
    rfl
  | succ n ih =>
    Hint (hidden := true) "Peel off the last term with
    `rw [Finset.sum_range_succ]`, then apply the inductive hypothesis
    with `rw [ih]`, and close with `ring`."
    rw [Finset.sum_range_succ, ih]
    ring

Conclusion
"
You proved a fresh inductive-sum identity. The proof structure is
identical to `∑ 1 = n`:

1. **`induction n with`** — split into base case and step.
2. **`rfl`** — the base case is trivial.
3. **`rw [sum_range_succ, ih]`** — peel off the last term and apply
   the hypothesis.
4. **`ring`** — close the arithmetic.

**Retrieval check**: You retrieved V3 (induction on range sums)
and V11 (peeling with `sum_range_succ`) on a new constant.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
