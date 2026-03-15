import GameServer.Commands
import Mathlib

World "RangeSumInduction"
Level 9

Title "Boss: A sum identity by induction"

Introduction
"
# Boss: Prove a sum identity by induction

Time to integrate everything you have learned in this world.

## The statement

Prove:
$$\\sum_{i=0}^{n-1} (4i + 3) = n(2n + 1)$$

In Lean: `∑ i ∈ range n, (4 * i + 3) = n * (2 * n + 1)`.

## Strategy

1. Set up induction on `n`.
2. **Base case**: both sides reduce to `0`. Use `rfl`.
3. **Inductive step**: You have
   `ih : ∑ i ∈ range n, (4 * i + 3) = n * (2 * n + 1)`.
   - Apply `sum_range_succ` to peel off the `(4n + 3)` term.
   - Apply `ih` to substitute the inner sum.
   - Close the arithmetic: verify
     `n * (2 * n + 1) + (4 * n + 3) = (n + 1) * (2 * (n + 1) + 1)`.

You may use either the compact `rw` style or an explicit `calc` block.
"

/-- The sum `∑ i ∈ range n, (4 * i + 3) = n * (2 * n + 1)`. -/
Statement (n : Nat) :
    ∑ i ∈ Finset.range n, (4 * i + 3) = n * (2 * n + 1) := by
  Hint "Start with `induction n with`."
  induction n with
  | zero =>
    Hint "Base case: both sides are `0`."
    Hint (hidden := true) "Use `rfl`."
    rfl
  | succ n ih =>
    Hint "Inductive step. You have
    `ih : ∑ i ∈ range n, (4 * i + 3) = n * (2 * n + 1)`.

    Peel off the last term with `rw [Finset.sum_range_succ]`, then
    apply `ih` with `rw [ih]`, and close with `ring`.

    Alternatively, write a `calc` block:
    ```
    calc ∑ i ∈ Finset.range (n + 1), (4 * i + 3)
        = (∑ i ∈ Finset.range n, (4 * i + 3)) + (4 * n + 3)
            := by rw [Finset.sum_range_succ]
      _ = n * (2 * n + 1) + (4 * n + 3) := by rw [ih]
      _ = (n + 1) * (2 * (n + 1) + 1) := by ring
    ```"
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, ih]` followed by `ring`."
    rw [Finset.sum_range_succ, ih]
    ring

Conclusion
"
Congratulations on completing the **Range Sum Induction** world!

You proved a non-trivial sum identity by induction, combining:
1. `induction n with` to set up the proof structure
2. `rfl` for the base case
3. `Finset.sum_range_succ` to peel off the last term
4. The inductive hypothesis `ih` to replace the inner sum
5. `ring` to close the polynomial arithmetic

## What you learned in this world

- **L01**: `Finset.range` review — `card_range`
- **L02**: `sum_range_succ` — the peeling-off lemma
- **L03**: First inductive sum — `∑ 1 = n`
- **L04**: The `calc` tactic for step-by-step equalities
- **L05**: `∑ 2 = 2n` — introducing `ring` in the inductive step
- **L06**: Sum of odd numbers — `∑ (2i+1) = n²`
- **L07**: Explicit `calc` walkthrough of the inductive step
- **L08**: Base case pitfalls — `range_zero` and `sum_empty`
- **L09**: Boss — integrating everything

## Transfer moment

In ordinary mathematics, you would write:

> *We prove by induction on n.*
>
> *Base case*: When $n = 0$, the sum is empty and equals $0$.
> Also $0 \\cdot (2 \\cdot 0 + 1) = 0$. ✓
>
> *Inductive step*: Assume $\\sum_{i=0}^{n-1}(4i+3) = n(2n+1)$.
> Then $\\sum_{i=0}^{n}(4i+3) = \\sum_{i=0}^{n-1}(4i+3) + (4n+3)
> = n(2n+1) + (4n+3) = (n+1)(2n+3) = (n+1)(2(n+1)+1)$. ✓

This is exactly what `sum_range_succ` + `induction` does in Lean.
The `rw [sum_range_succ]` step corresponds to \"peel off the last term\",
the `rw [ih]` step corresponds to \"apply the inductive hypothesis\",
and `ring` corresponds to \"verify the algebra\".

## What comes next

The next world will apply these techniques to a specific classic formula
in more depth.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
