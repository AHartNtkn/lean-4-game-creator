import Game.Metadata

World "GroupTutorial"
Level 3

Title "Right Inverse"

Introduction
"
Every element in a group has an **inverse**. If `a : G`, then `a⁻¹` is its
inverse. The superscript `⁻¹` is typed as `\\inv` or `\\-1` in Lean.

The theorem `mul_inv_cancel` says that `a * a⁻¹ = 1` — multiplying an
element by its inverse on the right gives the identity.

In this level, the goal is `a * a⁻¹ * b = b`. Remember that multiplication
is **left-associated**: this means `(a * a⁻¹) * b = b`. So `a * a⁻¹`
appears as a sub-expression on the left, and `mul_inv_cancel` applies to it.
"

/-- `mul_inv_cancel` says `a * a⁻¹ = 1` for any element `a` of a group.

Use it with `rw [mul_inv_cancel]` when you see `_ * _⁻¹` where
both sides are the same element.

Don't confuse with `inv_mul_cancel`, which handles `a⁻¹ * a`. -/
TheoremDoc mul_inv_cancel as "mul_inv_cancel" in "Group"

NewTheorem mul_inv_cancel

TheoremTab "Group"

Statement (G : Type*) [Group G] (a b : G) : a * a⁻¹ * b = b := by
  Hint "The goal is `a * a⁻¹ * b = b`, which means `(a * a⁻¹) * b = b`.
  The sub-expression `a * a⁻¹` matches `mul_inv_cancel`. Try `rw [mul_inv_cancel]`."
  rw [mul_inv_cancel]
  Hint "Now your goal should be `1 * b = b`. You know a theorem for this!"
  rw [one_mul]

Conclusion
"
Every element in a group has an inverse. `mul_inv_cancel` tells you
that `a * a⁻¹ = 1` — the element and its inverse cancel on the right.

Notice that `rw [mul_inv_cancel]` found the pattern `a * a⁻¹` inside
the larger expression `(a * a⁻¹) * b`. The `rw` tactic searches for
the pattern anywhere in the goal, not just at the top level.

But what about the other order? What is `a⁻¹ * a`?
"
