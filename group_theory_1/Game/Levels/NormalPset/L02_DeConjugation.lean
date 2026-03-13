import Game.Metadata

World "NormalPset"
Level 2

Title "De-conjugation"

Introduction
"
You know that normality lets you conjugate elements into `N`. But
what about undoing conjugation?

Given `a * b * a⁻¹ ∈ N`, can you recover `b ∈ N`? Yes — conjugate
*back* using normality. Since `N` is normal, you can conjugate
`a * b * a⁻¹` by `a⁻¹` (or by `a` using `conj_mem'`) to recover `b`.

Use `have` to store the conjugation result, then simplify step by step.
"

TheoremTab "Normal"

DisabledTactic simp group

Statement (G : Type*) [Group G] (N : Subgroup G) (hN : N.Normal)
    (a b : G) (h : a * b * a⁻¹ ∈ N) : b ∈ N := by
  Hint "Conjugate `a * b * a⁻¹` back to recover `b`. Use `conj_mem'`
  with conjugator `a`:
  `have h' := hN.conj_mem' (a * b * a⁻¹) h a`."
  Branch
    have h' := hN.conj_mem (a * b * a⁻¹) h a⁻¹
    Hint "You used `conj_mem` with conjugator `a⁻¹`. Now
    `{h'} : a⁻¹ * (a * b * a⁻¹) * (a⁻¹)⁻¹ ∈ N`. First clean up the
    double inverse: `rw [inv_inv] at {h'}`."
    rw [inv_inv] at h'
    Hint "Now reassociate: `rw [mul_assoc] at {h'}`."
    rw [mul_assoc] at h'
    Hint "Cancel on the right: `rw [inv_mul_cancel_right] at {h'}`."
    rw [inv_mul_cancel_right] at h'
    Hint "Cancel on the left: `rw [inv_mul_cancel_left] at {h'}`."
    rw [inv_mul_cancel_left] at h'
    exact h'
  have h' := hN.conj_mem' (a * b * a⁻¹) h a
  Hint "Now `{h'} : a⁻¹ * (a * b * a⁻¹) * a ∈ N`. Reassociate:
  `rw [mul_assoc] at {h'}`."
  rw [mul_assoc] at h'
  Hint "Cancel `a⁻¹ * a` on the right:
  `rw [inv_mul_cancel_right] at {h'}`."
  rw [inv_mul_cancel_right] at h'
  Hint "Cancel `a⁻¹ * a` on the left:
  `rw [inv_mul_cancel_left] at {h'}`."
  rw [inv_mul_cancel_left] at h'
  Hint (hidden := true) "Now `{h'} : b ∈ N`. `exact {h'}`."
  exact h'

Conclusion
"
**De-conjugation**: if `gng⁻¹ ∈ N` and `N` is normal, you can
recover `n ∈ N` by conjugating back.

On paper: *Since `aba⁻¹ ∈ N` and `N` is normal, conjugate by `a⁻¹`:
`a⁻¹(aba⁻¹)a = b ∈ N`.*

Normality works both ways: it lets you conjugate elements *into* `N`
(the definition) and also *de-conjugate* elements out of the
conjugation wrapper.

In fact, for a normal subgroup, the map `n ↦ gng⁻¹` is a *bijection*
from `N` to `N` — it maps `N` into `N` (normality) and is invertible
(de-conjugation). This bijection is called an **inner automorphism**.
"
