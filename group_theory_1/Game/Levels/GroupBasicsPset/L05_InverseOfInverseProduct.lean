import Game.Metadata

World "GroupBasicsPset"
Level 5

Title "Inverse of an Inverse Product"

Introduction
"
Simplify `(a⁻¹ * b)⁻¹`. Two lemmas from Group Basics should be enough.
"

DisabledTactic group

TheoremTab "Cancel"

Statement (G : Type*) [Group G] (a b : G) : (a⁻¹ * b)⁻¹ = b⁻¹ * a := by
  Hint "What does `mul_inv_rev` tell you about `(a⁻¹ * b)⁻¹`? After
  expanding, look for a double inverse to simplify."
  Hint (hidden := true) "`rw [mul_inv_rev]` gives `b⁻¹ * (a⁻¹)⁻¹`.
  Then `rw [inv_inv]` simplifies `(a⁻¹)⁻¹` to `a`."
  Branch
    -- apply approach
    apply inv_eq_of_mul_eq_one_right
    rw [mul_assoc, mul_inv_cancel_left, inv_mul_cancel]
  Branch
    -- calc proof
    calc (a⁻¹ * b)⁻¹
        _ = b⁻¹ * (a⁻¹)⁻¹   := by rw [mul_inv_rev]
        _ = b⁻¹ * a           := by rw [inv_inv]
  rw [mul_inv_rev, inv_inv]

Conclusion
"
Two rewrites: shoes-and-socks to distribute the inverse, then double
inverse to clean up.

Notice you had a choice here: you could also
`apply inv_eq_of_mul_eq_one_right` and verify the multiplication, as
you did for the Group Basics boss. Both approaches work. The rewrite
path is shorter when you already know the answer and just need to
simplify; the apply-and-verify path is better when the answer isn't
obvious and you need to discover it through calculation.
"
