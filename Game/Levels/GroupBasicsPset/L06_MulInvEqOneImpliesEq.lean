import Game.Metadata

World "GroupBasicsPset"
Level 6

Title "Cancelling via Inverses"

Introduction
"
If `a * b⁻¹ = 1`, what can you conclude about `a` and `b`?

This problem requires combining two tools from Group Basics:
inverse uniqueness and the injectivity of inversion.
"

DisabledTactic group

TheoremTab "Cancel"

Statement (G : Type*) [Group G] (a b : G) (h : a * b⁻¹ = 1) :
    a = b := by
  Hint "From `a * b⁻¹ = 1`, inverse uniqueness tells you `a⁻¹ = b⁻¹`.
  What theorem lets you conclude `a = b` from `a⁻¹ = b⁻¹`?"
  Hint (hidden := true) "Use `apply inv_inj.mp` to change the goal to
  `a⁻¹ = b⁻¹`, then `exact inv_eq_of_mul_eq_one_right h` closes it."
  Branch
    -- One-liner
    exact inv_inj.mp (inv_eq_of_mul_eq_one_right h)
  Branch
    -- calc proof using inv_inv
    calc a = (a⁻¹)⁻¹   := by rw [inv_inv]
         _ = (b⁻¹)⁻¹   := by rw [inv_eq_of_mul_eq_one_right h]
         _ = b           := by rw [inv_inv]
  apply inv_inj.mp
  Hint "The goal is now `a⁻¹ = b⁻¹`. You have `h : a * b⁻¹ = 1`.
  What does `inv_eq_of_mul_eq_one_right` give you?"
  exact inv_eq_of_mul_eq_one_right h

Conclusion
"
Two tools, two steps: `inv_eq_of_mul_eq_one_right` deduces
`a⁻¹ = b⁻¹` from `a * b⁻¹ = 1`, and `inv_inj` strips the inverses.

This is your first use of `inv_inj` — the fact that inversion is
injective (`a⁻¹ = b⁻¹ → a = b`). It follows immediately from
`inv_inv`: apply inversion to both sides and the double inverses
cancel. Keep it in mind for future problems involving inverse
equalities.
"
