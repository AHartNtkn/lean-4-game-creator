import GameServer.Commands
import Mathlib

World "RangeSumInduction"
Level 5

Title "A slightly harder sum"

Introduction
"
# Summing a constant: `∑ i ∈ range n, 2 = 2 * n`

In the last two levels, the arithmetic after `rw [sum_range_succ, ih]`
was trivial — both sides were already equal. This time, you will need
the `ring` tactic to close the final step.

## The statement

Prove: `∑ i ∈ range n, 2 = 2 * n`.

## Strategy

1. `induction n with`
2. Base case: `rfl` (both sides are `0`)
3. Inductive step:
   - `rw [sum_range_succ, ih]` leaves `2 * n + 2 = 2 * (n + 1)`
   - `ring` closes this

You can also use `calc` if you prefer to make each step explicit.
"

/-- The sum of `n` twos is `2 * n`. -/
Statement (n : Nat) : ∑ i ∈ Finset.range n, 2 = 2 * n := by
  Hint "Start with `induction n with`."
  induction n with
  | zero =>
    Hint (hidden := true) "Use `rfl`."
    rfl
  | succ n ih =>
    Hint "Peel off the last term and apply the inductive hypothesis:
    `rw [Finset.sum_range_succ, ih]`.
    Then close the arithmetic with `ring`."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, ih]` followed by `ring`."
    rw [Finset.sum_range_succ, ih]
    Hint "The goal is now `2 * n + 2 = 2 * (n + 1)`. Use `ring` to
    close it."
    Hint (hidden := true) "Use `ring`."
    ring

Conclusion
"
You proved `∑ i ∈ range n, 2 = 2 * n` by induction.

## The emerging pattern

The three-step template is becoming clear:

1. `induction n with`
2. Base case: `rfl`
3. Inductive step: `rw [sum_range_succ, ih]`, then `ring` (or `omega`)

The only thing that changes between proofs is the **final arithmetic
step**. As long as you can close the algebra, the structure is the same.

## `ring` vs `omega`

- **`ring`**: handles polynomial equalities (`2 * n + 2 = 2 * (n + 1)`,
  `n^2 + 2*n + 1 = (n+1)^2`).
- **`omega`**: handles linear arithmetic with `+`, `-`, `*` by constants,
  and inequalities.

For sum identities, `ring` is usually the right choice in the
inductive step.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
