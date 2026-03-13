import Game.Metadata

open scoped Pointwise

World "CosetBasics"
Level 4

Title "From Equality to Membership"

Introduction
"
Combine the two unfolding lemmas: if two cosets are equal, then each
representative belongs to the other coset.

Given `a • H = b • H`, prove `b ∈ a • H`.
"

/-- Disabled — use `mem_leftCoset_iff` and algebra instead. -/
TheoremDoc mem_leftCoset as "mem_leftCoset" in "Coset"

/-- Disabled — use `mem_leftCoset_iff` and algebra instead. -/
TheoremDoc mem_own_leftCoset as "mem_own_leftCoset" in "Coset"

/-- Disabled — prove coset equality from `leftCoset_eq_iff` instead. -/
TheoremDoc leftCoset_mem_leftCoset as "leftCoset_mem_leftCoset" in "Coset"

TheoremTab "Coset"

DisabledTactic simp group
DisabledTheorem mem_leftCoset mem_own_leftCoset leftCoset_mem_leftCoset

Statement (G : Type*) [Group G] (H : Subgroup G) (a b : G)
    (h : a • (H : Set G) = b • (H : Set G)) :
    b ∈ a • (H : Set G) := by
  Hint "You need `b ∈ a • H`. Unfold coset membership:
  `rw [mem_leftCoset_iff]`."
  Branch
    rw [leftCoset_eq_iff] at h
    Hint "You unfolded the hypothesis first — that works too.
    Now unfold the goal: `rw [mem_leftCoset_iff]`."
    rw [mem_leftCoset_iff]
    Hint (hidden := true) "`exact {h}`."
    exact h
  rw [mem_leftCoset_iff]
  Hint "The goal is `a⁻¹ * b ∈ ↑H`. Extract this from the coset equality:
  `rw [leftCoset_eq_iff] at {h}`."
  rw [leftCoset_eq_iff] at h
  Hint (hidden := true) "`exact {h}`."
  exact h

Conclusion
"
If `aH = bH`, then `b ∈ aH`. The proof combines both unfolding lemmas:
`leftCoset_eq_iff` extracts `a⁻¹ * b ∈ H` from the equality, and
`mem_leftCoset_iff` reduces the membership goal to the same condition.

Both directions used the unfold-cancel-close pattern — just pointed
at different targets (hypothesis vs goal).
"
