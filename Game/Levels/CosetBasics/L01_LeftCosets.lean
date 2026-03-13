import Game.Metadata

open scoped Pointwise

World "CosetBasics"
Level 1

Title "Left Coset Membership"

Introduction
"
Subgroups partition a group into pieces of equal size called **cosets**.
Understanding cosets is the key to Lagrange's theorem (every subgroup's
order divides the group's order) and to quotient groups.

If `H` is a subgroup of `G` and `a` is any element of `G`, the **left
coset** of `H` by `a` is the set

`aH = {a * h | h ∈ H}`

In Lean, left cosets are written `a • (H : Set G)` using the scalar
multiplication notation `•` (typed `\\smul` or `\\bu`).

The key unfolding lemma is:

`mem_leftCoset_iff : x ∈ a • (H : Set G) ↔ a⁻¹ * x ∈ H`

To check whether `x` is in the coset `aH`, ask: *is `a⁻¹ * x` in `H`?*

Prove that `a * h` belongs to the left coset `a • H` when `h ∈ H`.
"

/-- `mem_leftCoset_iff` says:

`x ∈ a • (H : Set G) ↔ a⁻¹ * x ∈ H`

Use `rw [mem_leftCoset_iff]` to unfold coset membership. -/
TheoremDoc mem_leftCoset_iff as "mem_leftCoset_iff" in "Coset"

NewTheorem mem_leftCoset_iff

/-- Disabled — use `mem_leftCoset_iff` and algebra instead. -/
TheoremDoc mem_leftCoset as "mem_leftCoset" in "Coset"

/-- Disabled — use `mem_leftCoset_iff` and algebra instead. -/
TheoremDoc mem_own_leftCoset as "mem_own_leftCoset" in "Coset"

TheoremTab "Coset"

DisabledTactic simp group
DisabledTheorem mem_leftCoset mem_own_leftCoset

Statement (G : Type*) [Group G] (H : Subgroup G) (a x : G) (hx : x ∈ H) :
    a * x ∈ a • (H : Set G) := by
  Hint "Unfold coset membership: `rw [mem_leftCoset_iff]`."
  rw [mem_leftCoset_iff]
  Hint "The goal is `a⁻¹ * (a * x) ∈ ↑H`. Cancel `a⁻¹ * a`:
  `rw [inv_mul_cancel_left]`."
  rw [inv_mul_cancel_left]
  Hint (hidden := true) "`exact {hx}`."
  exact hx

Conclusion
"
To check `y ∈ a • H`, unfold with `mem_leftCoset_iff` to get `a⁻¹ * y ∈ H`,
then simplify. The pattern: **unfold**, **cancel**, **close**.
"
