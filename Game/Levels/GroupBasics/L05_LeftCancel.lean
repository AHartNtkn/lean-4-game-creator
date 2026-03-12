import Game.Metadata

World "GroupBasics"
Level 5

Title "Left Cancellation Law"

Introduction
"
If `a * b = a * c`, can you conclude `b = c`? In a group, yes —
this is the **left cancellation law**.

The proof formalizes a move you already know from algebra:
**multiply both sides by the same thing**. To cancel `a` on the left,
multiply both sides by `a⁻¹`. In `calc`, this means rewriting both
sides using `inv_mul_cancel_left`.

There's a new Lean skill here: **rewriting with a hypothesis**.

You've used `rw [mul_one]` to rewrite with a named theorem. You can
also use `rw [h]` where `h` is a hypothesis in your context. If
`h : a * b = a * c`, then `rw [h]` replaces `a * b` with `a * c`
(or use `rw [← h]` for the reverse direction).
"

/-- `mul_left_cancel` says that if `a * b = a * c`, then `b = c`.

This is the **left cancellation law**: you can cancel a common left
factor in a group.

To use it: `exact mul_left_cancel h` where `h : a * b = a * c`. -/
TheoremDoc mul_left_cancel as "mul_left_cancel" in "Cancel"

NewTheorem mul_left_cancel

DisabledTactic group

TheoremTab "Cancel"

Statement (G : Type*) [Group G] (a b c : G) (h : a * b = a * c) :
    b = c := by
  Hint "You need to show `b = c`. The hypothesis `h` tells you
  `a * b = a * c`. The idea: express both `b` and `c` in terms of
  `a⁻¹ * (a * _)`, then use `h` to connect them.

  Start a `calc` block:
  ```
  calc b = a⁻¹ * (a * b) := by rw [inv_mul_cancel_left]
       _ = ...
  ```"
  Hint (hidden := true) "The full proof:
  ```
  calc b = a⁻¹ * (a * b) := by rw [inv_mul_cancel_left]
       _ = a⁻¹ * (a * c) := by rw [h]
       _ = c              := by rw [inv_mul_cancel_left]
  ```"
  Branch
    -- Direct exact approach (for experienced players)
    exact mul_left_cancel h
  -- calc proof (primary)
  calc b = a⁻¹ * (a * b) := by rw [inv_mul_cancel_left]
       _ = a⁻¹ * (a * c) := by rw [h]
       _ = c              := by rw [inv_mul_cancel_left]

Conclusion
"
The key new skill: **rewriting with a hypothesis**. When `h` is in
your context, `rw [h]` uses it just like a named theorem.

In the next level, you'll prove the mirror image: right cancellation.
"
