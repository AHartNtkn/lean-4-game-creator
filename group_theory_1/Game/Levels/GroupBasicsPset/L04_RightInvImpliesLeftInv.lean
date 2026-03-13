import Game.Metadata

World "GroupBasicsPset"
Level 4

Title "Right Inverse Implies Left Inverse"

Introduction
"
If `a * b = 1`, does `b * a = 1` follow?

In a general monoid, no — right inverses need not be left inverses.
But in a group, you have enough structure to force it.

This is the first problem where you need to combine tools in a way
you haven't seen before.
"

DisabledTactic group

TheoremTab "Cancel"

Statement (G : Type*) [Group G] (a b : G) (h : a * b = 1) : b * a = 1 := by
  Hint "You know `a * b = 1`. From inverse uniqueness
  (`inv_eq_of_mul_eq_one_right`), this tells you `a⁻¹ = b`. Can you use
  a backward rewrite to replace `b` with `a⁻¹` in the goal?"
  Hint (hidden := true) "Use `rw [← inv_eq_of_mul_eq_one_right h]` to
  replace `b` with `a⁻¹`. The goal becomes `a⁻¹ * a = 1`, which is
  `inv_mul_cancel`."
  Branch
    -- calc proof
    calc b * a = a⁻¹ * a   := by rw [← inv_eq_of_mul_eq_one_right h]
         _ = 1              := by rw [inv_mul_cancel]
  rw [← inv_eq_of_mul_eq_one_right h, inv_mul_cancel]

Conclusion
"
The key insight: `a * b = 1` tells you `b = a⁻¹` (by inverse
uniqueness), and then `b * a = a⁻¹ * a = 1` by `inv_mul_cancel`.

This is why groups are special: right inverses are automatically left
inverses. Combined with inverse uniqueness from Group Basics, this
means every group element has exactly one **two-sided** inverse — a
fact so fundamental that it's easy to take for granted. In a monoid,
you'd be stuck.

The converse — if `b * a = 1` then `a * b = 1` — follows by the same
argument with the roles swapped. So `a * b = 1` and `b * a = 1` are
equivalent statements in a group.
"
