import Game.Metadata

open scoped Pointwise

World "CosetBasics"
Level 2

Title "Self-Membership"

Introduction
"
Every element belongs to its own coset: `a ∈ aH`.

This follows from `mem_leftCoset_iff`: you need `a⁻¹ * a ∈ H`,
which is `1 ∈ H`.
"

/-- Disabled — use `mem_leftCoset_iff` and algebra instead. -/
TheoremDoc mem_leftCoset as "mem_leftCoset" in "Coset"

/-- Disabled — use `mem_leftCoset_iff` and algebra instead. -/
TheoremDoc mem_own_leftCoset as "mem_own_leftCoset" in "Coset"

TheoremTab "Coset"

DisabledTactic simp group
DisabledTheorem mem_leftCoset mem_own_leftCoset

Statement (G : Type*) [Group G] (H : Subgroup G) (a : G) :
    a ∈ a • (H : Set G) := by
  Hint "Unfold coset membership: `rw [mem_leftCoset_iff]`."
  rw [mem_leftCoset_iff]
  Hint "The goal is `a⁻¹ * a ∈ ↑H`. Cancel: `rw [inv_mul_cancel]`."
  rw [inv_mul_cancel]
  Hint (hidden := true) "`exact H.one_mem`."
  exact H.one_mem

Conclusion
"
Every element belongs to its own coset because `a⁻¹ * a = 1 ∈ H`.

On paper: `a = a · 1 ∈ aH` since `1 ∈ H`.

This is the same unfold-cancel-close pattern from Level 1, with
the cancellation `a⁻¹ * a = 1` instead of `a⁻¹ * (a * h) = h`.
"
