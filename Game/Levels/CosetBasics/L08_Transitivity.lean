import Game.Metadata

World "CosetBasics"
Level 8

Title "Transitivity"

Introduction
"
**Transitivity**: If `a⁻¹ * b ∈ H` and `b⁻¹ * c ∈ H`, then
`a⁻¹ * c ∈ H`.

The key insight: `a⁻¹ * c = (a⁻¹ * b) * (b⁻¹ * c)`.

To get this factoring, insert `b * b⁻¹ = 1` between `a⁻¹` and `c`:
1. Rewrite `c` as `b * (b⁻¹ * c)` using `← mul_inv_cancel_left`
2. Reassociate with `← mul_assoc`
3. Apply `mul_mem`
"

TheoremTab "Coset"

DisabledTactic simp group

Statement (G : Type*) [Group G] (H : Subgroup G) (a b c : G)
    (h1 : a⁻¹ * b ∈ H) (h2 : b⁻¹ * c ∈ H) :
    a⁻¹ * c ∈ H := by
  Hint "Rewrite `c` as `b * (b⁻¹ * c)`: `rw [← mul_inv_cancel_left b c]`."
  rw [← mul_inv_cancel_left b c]
  Hint "Reassociate: `rw [← mul_assoc]`.
  The goal becomes `(a⁻¹ * b) * (b⁻¹ * c) ∈ H`."
  rw [← mul_assoc]
  Hint (hidden := true) "`exact H.mul_mem {h1} {h2}`."
  exact H.mul_mem h1 h2

Conclusion
"
The **insert-cancel** pattern: insert `b · b⁻¹` to factor
`a⁻¹c = (a⁻¹b)(b⁻¹c)`, then use `mul_mem`.

On paper: if `a⁻¹b ∈ H` and `b⁻¹c ∈ H`, then
`a⁻¹c = (a⁻¹b)(b⁻¹c) ∈ H` by closure under multiplication.
"
