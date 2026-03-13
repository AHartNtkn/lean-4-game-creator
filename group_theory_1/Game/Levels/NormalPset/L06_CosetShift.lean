import Game.Metadata

open scoped Pointwise

World "NormalPset"
Level 6

Title "Coset Shift"

Introduction
"
Multiplying a coset representative by an element of `N` doesn't
change the coset.

Given `n ∈ N`, prove `(a * n) • N = a • N`.

Reduce coset equality to subgroup membership using `leftCoset_eq_iff`,
then simplify the algebra.
"

TheoremTab "Normal"

DisabledTactic simp group

Statement (G : Type*) [Group G] (N : Subgroup G)
    (a n : G) (hn : n ∈ N) :
    (a * n) • (N : Set G) = a • (N : Set G) := by
  Hint "Reduce coset equality to subgroup membership:
  `rw [leftCoset_eq_iff]`.
  The goal becomes `(a * n)⁻¹ * a ∈ N`."
  rw [leftCoset_eq_iff]
  Hint "The goal is `(a * n)⁻¹ * a ∈ N`. Expand the inverse:
  `rw [mul_inv_rev]`.
  This gives `n⁻¹ * a⁻¹ * a ∈ N`."
  rw [mul_inv_rev]
  Hint "Now `n⁻¹ * a⁻¹ * a ∈ N`. Cancel `a⁻¹ * a`:
  `rw [inv_mul_cancel_right]`."
  Branch
    rw [mul_assoc, inv_mul_cancel, mul_one]
    exact N.inv_mem hn
  rw [inv_mul_cancel_right]
  Hint (hidden := true) "The goal is `n⁻¹ ∈ N`.
  `exact N.inv_mem {hn}`."
  exact N.inv_mem hn

Conclusion
"
**Representative absorption**: multiplying a coset representative by
an element of `N` doesn't change the coset.

On paper: *`(an)⁻¹ · a = n⁻¹a⁻¹a = n⁻¹ ∈ N`, so `(an)N = aN`.*

Notice that normality was **not needed** here — this works for any
subgroup. The proof only used `inv_mem` (subgroup closure under
inverses), not the conjugation property.

So where does normality actually matter? When you want coset
*multiplication* to be well-defined. If `a' = an₁` is another
representative of `aN`, then `a'b = an₁b = ab · (b⁻¹n₁b)`. For
`a'b` to land in `(ab)N`, you need `b⁻¹n₁b ∈ N` — which is
exactly the conjugation condition. Without normality, different
representatives give different products.
"
