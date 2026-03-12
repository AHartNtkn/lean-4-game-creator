import Game.Metadata

World "GroupBasics"
Level 8

Title "Double Inverse"

Introduction
"
What happens when you take the inverse of an inverse? You get back
the original: `(a⁻¹)⁻¹ = a`. This is the **involution** property
of inversion.

In this level, you'll use the `apply` tactic together with
`inv_eq_of_mul_eq_one_right` from the previous level. The strategy:

1. `apply inv_eq_of_mul_eq_one_right` — this transforms the goal
   from `(a⁻¹)⁻¹ = a` to `a⁻¹ * a = 1` (since if `a⁻¹ * a = 1`,
   then `(a⁻¹)⁻¹ = a` by uniqueness)
2. Close the new goal with `inv_mul_cancel`

The `apply` tactic works backwards: if the goal is `P` and you have
a theorem `T : Q → P`, then `apply T` changes the goal to `Q`.
"

/-- `inv_inv` says `(a⁻¹)⁻¹ = a` — taking the inverse twice gives
back the original element.

Use it with `rw [inv_inv]` to simplify double inverses. -/
TheoremDoc inv_inv as "inv_inv" in "Cancel"

/-- `inv_inj` says `a⁻¹ = b⁻¹ ↔ a = b` — the inverse function is
injective.

Use the `→` direction with `exact inv_inj.mp h` to go from
`a⁻¹ = b⁻¹` to `a = b`. -/
TheoremDoc inv_inj as "inv_inj" in "Cancel"

NewTheorem inv_inv inv_inj

DisabledTactic group

TheoremTab "Cancel"

Statement (G : Type*) [Group G] (a : G) : (a⁻¹)⁻¹ = a := by
  Hint "The goal is `(a⁻¹)⁻¹ = a`. By inverse uniqueness, it suffices
  to show `a⁻¹ * a = 1`.

  Use `apply inv_eq_of_mul_eq_one_right` to transform the goal."
  Branch
    -- calc proof (alternative)
    calc (a⁻¹)⁻¹ = (a⁻¹)⁻¹ * 1       := by rw [mul_one]
         _ = (a⁻¹)⁻¹ * (a⁻¹ * a)      := by rw [inv_mul_cancel]
         _ = a                          := by rw [inv_mul_cancel_left]
  Branch
    -- Direct exact
    exact inv_inv a
  apply inv_eq_of_mul_eq_one_right
  Hint "The goal is now `a⁻¹ * a = 1`. You know this — it's
  `inv_mul_cancel`."
  exact inv_mul_cancel a

Conclusion
"
You just used the `apply` pattern for the first time: transform the
goal using a theorem that works backwards, then close the simpler
new goal.

Here: `apply inv_eq_of_mul_eq_one_right` turned `(a⁻¹)⁻¹ = a` into
`a⁻¹ * a = 1`, which `inv_mul_cancel` closes immediately.

`inv_inj` (`a⁻¹ = b⁻¹ ↔ a = b`) is also now in your inventory.
It follows immediately from `inv_inv`: if `a⁻¹ = b⁻¹`, apply
`(·)⁻¹` to both sides and use `inv_inv` twice to get `a = b`.

You're ready for the boss.
"
