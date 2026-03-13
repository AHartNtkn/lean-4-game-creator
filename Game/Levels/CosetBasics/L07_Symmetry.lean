import Game.Metadata

World "CosetBasics"
Level 7

Title "Symmetry"

Introduction
"
**Symmetry**: If `a⁻¹ * b ∈ H`, then `b⁻¹ * a ∈ H`.

The key insight: `b⁻¹ * a = (a⁻¹ * b)⁻¹`, and subgroups are closed
under inverses.

To rewrite `b⁻¹ * a` as `(a⁻¹ * b)⁻¹`, work backwards:
1. Rewrite `a` as `(a⁻¹)⁻¹` using `← inv_inv`
2. Recognize `b⁻¹ * (a⁻¹)⁻¹` as `(a⁻¹ * b)⁻¹` using `← mul_inv_rev`
"

TheoremTab "Coset"

DisabledTactic simp group

Statement (G : Type*) [Group G] (H : Subgroup G) (a b : G)
    (h : a⁻¹ * b ∈ H) :
    b⁻¹ * a ∈ H := by
  Hint "Rewrite `a` as `(a⁻¹)⁻¹`: `rw [← inv_inv a]`."
  rw [← inv_inv a]
  Hint "Now `b⁻¹ * (a⁻¹)⁻¹` matches `← mul_inv_rev`.
  Rewrite: `rw [← mul_inv_rev]`."
  rw [← mul_inv_rev]
  Hint "The goal is `(a⁻¹ * b)⁻¹ ∈ H`. Apply inverse closure:
  `exact H.inv_mem {h}`."
  exact H.inv_mem h

Conclusion
"
The **inverse-flip** pattern: `b⁻¹ * a = (a⁻¹ * b)⁻¹`.

The rewrite sequence `← inv_inv` then `← mul_inv_rev` is the standard
way to express this in Lean. Then `inv_mem` closes the goal.

On paper: if `a⁻¹b ∈ H`, then `b⁻¹a = (a⁻¹b)⁻¹ ∈ H` since `H` is
closed under inverses.
"
