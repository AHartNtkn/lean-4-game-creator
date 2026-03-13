import Game.Metadata

open scoped Pointwise

World "CosetBasics"
Level 5

Title "From Membership to Equality"

Introduction
"
Level 4 showed: if `aH = bH`, then `b ∈ aH`.

Now prove the **converse**: if `b ∈ aH`, then `aH = bH`.

This completes the fundamental equivalence: `b ∈ aH ↔ aH = bH`.
Two cosets are equal precisely when they share an element — any element
of a coset can serve as its representative.

The proof uses the same two lemmas as Level 4, but applied in opposite
directions.
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
    (h : b ∈ a • (H : Set G)) :
    a • (H : Set G) = b • (H : Set G) := by
  Hint "Unfold the hypothesis: `rw [mem_leftCoset_iff] at {h}`."
  Branch
    rw [leftCoset_eq_iff]
    Hint "You reduced the goal first — that works too.
    Now unfold the hypothesis: `rw [mem_leftCoset_iff] at {h}`."
    rw [mem_leftCoset_iff] at h
    Hint (hidden := true) "`exact {h}`."
    exact h
  rw [mem_leftCoset_iff] at h
  Hint "Now `{h} : a⁻¹ * b ∈ ↑H`. Reduce the goal:
  `rw [leftCoset_eq_iff]`."
  rw [leftCoset_eq_iff]
  Hint (hidden := true) "`exact {h}`."
  exact h

Conclusion
"
Combined with Level 4, you've shown:

`b ∈ aH  ↔  aH = bH`

Any element of a coset can serve as its representative. This is why
cosets form a partition: each element of `G` belongs to exactly one
coset, and any element of that coset names it.
"
