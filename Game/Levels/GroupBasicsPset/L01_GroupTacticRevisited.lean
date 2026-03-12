import Game.Metadata

World "GroupBasicsPset"
Level 1

Title "The `group` Tactic Returns"

Introduction
"
Welcome to the **Group Basics Problem Set** — your first practice world.

In Group Basics, you proved everything by hand with `group` disabled.
Now it's back. This first problem is a warm-up to remind you of its
power.

Simplify `a * (b * a)⁻¹`. Try the `group` tactic.
"

TheoremTab "Cancel"

Statement (G : Type*) [Group G] (a b : G) : a * (b * a)⁻¹ = b⁻¹ := by
  Hint "The `group` tactic is back! It closes any equation that follows
  from the group axioms. Try it."
  Branch
    -- Manual proof using cancel_left
    rw [mul_inv_rev, mul_inv_cancel_left]
  group

Conclusion
"
One tactic, one step. Under the hood, `group` searches for a sequence
of rewrites using exactly the axioms and identities you proved by hand
in Group Basics. Every manual proof you wrote there is a step that
`group` can now take for you.

For the rest of this problem set, `group` will be **disabled** so you
can practice the manual techniques. Think of this level as a reminder
of what's waiting when the training wheels come off.
"
