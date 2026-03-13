import Game.Metadata

World "CosetBasics"
Level 6

Title "Reflexivity"

Introduction
"
The relation `a ~ b ↔ a⁻¹ * b ∈ H` is an equivalence relation on `G`.
The equivalence classes are exactly the left cosets.

We'll prove the three properties — reflexivity, symmetry, and
transitivity — separately, then combine them in the boss level.

**Reflexivity**: `a⁻¹ * a ∈ H` for any `a`.

You already proved this in Level 2 — there, `mem_leftCoset_iff` reduced
`a ∈ aH` to `a⁻¹ * a ∈ H`. Now you prove the same fact directly,
without coset notation. The equivalence relation and coset membership
are two views of the same thing.
"

TheoremTab "Coset"

DisabledTactic simp group

Statement (G : Type*) [Group G] (H : Subgroup G) (a : G) :
    a⁻¹ * a ∈ H := by
  Hint "Cancel `a⁻¹ * a`: `rw [inv_mul_cancel]`."
  rw [inv_mul_cancel]
  Hint (hidden := true) "`exact H.one_mem`."
  exact H.one_mem

Conclusion
"
Reflexivity is immediate: `a⁻¹ * a = 1 ∈ H`.

On paper: `a ~ a` because `a⁻¹a = 1 ∈ H` (the identity is in every
subgroup).
"
