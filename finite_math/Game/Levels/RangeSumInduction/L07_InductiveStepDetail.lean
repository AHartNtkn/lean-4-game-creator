import GameServer.Commands
import Mathlib

World "RangeSumInduction"
Level 7

Title "Inductive step in detail"

Introduction
"
# Walking through the inductive step with `calc`

In the previous levels, the inductive step was always:
`rw [sum_range_succ, ih]` then `ring`. Let us slow down and use `calc`
to make every step visible.

## The statement

Prove: `∑ i ∈ range n, 2 = 2 * n`.

You already proved this in Level 5, but this time you must use `calc`
in the inductive step:

```
calc ∑ i ∈ Finset.range (n + 1), 2
    = (∑ i ∈ Finset.range n, 2) + 2 := by rw [Finset.sum_range_succ]
  _ = 2 * n + 2 := by rw [ih]
  _ = 2 * (n + 1) := by ring
```

Each line isolates one conceptual step:
1. **Peel off** the last term (`sum_range_succ`).
2. **Substitute** the inductive hypothesis (`ih`).
3. **Close** the arithmetic (`ring`).
"

/-- Sum of `n` twos is `2 * n`, proved step-by-step with `calc`. -/
Statement (n : Nat) : ∑ i ∈ Finset.range n, 2 = 2 * n := by
  Hint "Start with `induction n with`."
  induction n with
  | zero =>
    Hint (hidden := true) "Use `rfl`."
    rfl
  | succ n ih =>
    Hint "Use a `calc` block with three steps:
    1. Apply `sum_range_succ` to peel off the last `2`.
    2. Rewrite with `ih` to replace the inner sum by `2 * n`.
    3. Use `ring` to verify `2 * n + 2 = 2 * (n + 1)`.

    ```
    calc ∑ i ∈ Finset.range (n + 1), 2
        = (∑ i ∈ Finset.range n, 2) + 2 := by rw [Finset.sum_range_succ]
      _ = 2 * n + 2 := by rw [ih]
      _ = 2 * (n + 1) := by ring
    ```"
    calc ∑ i ∈ Finset.range (n + 1), 2
        = (∑ i ∈ Finset.range n, 2) + 2 := by rw [Finset.sum_range_succ]
      _ = 2 * n + 2 := by rw [ih]
      _ = 2 * (n + 1) := by ring

Conclusion
"
You wrote the inductive step as an explicit chain of equalities.

## When is `calc` worth the extra lines?

- **Debugging**: If `ring` fails after `rw [sum_range_succ, ih]`, a
  `calc` block helps you see exactly where things go wrong.
- **Readability**: For proofs you or others will revisit, `calc` makes
  the reasoning transparent.
- **Complex algebra**: When the final `ring` step involves several
  algebraic manipulations, intermediate steps can help.

## The boss preparation

The boss will ask you to prove a new identity by induction. You can
use either the compact `rw` style or the explicit `calc` style —
whichever you prefer.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
