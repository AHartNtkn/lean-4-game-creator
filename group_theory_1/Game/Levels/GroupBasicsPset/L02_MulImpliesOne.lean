import Game.Metadata

World "GroupBasicsPset"
Level 2

Title "If `a * b = a`, then `b = 1`"

Introduction
"
If `a * b = a`, what must `b` be? The answer is obvious — `b = 1` —
but proving it requires a specific technique from your toolkit.

Hint: compare `a * b` with `a * 1`.
"

DisabledTactic group

TheoremTab "Cancel"

Statement (G : Type*) [Group G] (a b : G) (h : a * b = a) : b = 1 := by
  Hint "The hypothesis says `a * b = a`. Compare this to `mul_one`:
  `a * 1 = a`. So `a * b = a * 1`. What does left cancellation give you?

  **Lean tip**: when `apply` can't figure out which element to cancel,
  you can specify it with a **named argument**: `apply mul_left_cancel (a := a)`
  tells Lean that the common left factor is `a`."
  Hint (hidden := true) "Use `apply mul_left_cancel (a := a)` to reduce
  the goal to `a * b = a * 1`. Then `rw [h, mul_one]` closes it."
  Branch
    -- calc proof
    calc b = a⁻¹ * (a * b)   := by rw [inv_mul_cancel_left]
         _ = a⁻¹ * a         := by rw [h]
         _ = 1                := by rw [inv_mul_cancel]
  apply mul_left_cancel (a := a)
  Hint "The goal is now `a * b = a * 1`. You have `h : a * b = a` and
  `mul_one : a * 1 = a`."
  rw [h, mul_one]

Conclusion
"
The key move: recognize `a * b = a` as `a * b = a * 1`, then apply
left cancellation. Same technique from Group Basics, new surface form.
"
