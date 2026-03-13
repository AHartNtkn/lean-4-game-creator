import Game.Metadata

open scoped Pointwise

World "CosetBasics"
Level 3

Title "Coset Equality"

Introduction
"
When are two cosets `aH` and `bH` equal?

`leftCoset_eq_iff : a • (H : Set G) = b • (H : Set G) ↔ a⁻¹ * b ∈ H`

Two cosets are equal when their representatives differ by an element
of `H`.

We call `a` a *representative* of the coset `aH` — any element of
the coset can serve as its representative.

Prove that multiplying a representative by an element of `H` doesn't
change the coset.
"

/-- `leftCoset_eq_iff` says:

`a • (H : Set G) = b • (H : Set G) ↔ a⁻¹ * b ∈ H`

Use `rw [leftCoset_eq_iff]` to reduce coset equality to subgroup
membership. -/
TheoremDoc leftCoset_eq_iff as "leftCoset_eq_iff" in "Coset"

NewTheorem leftCoset_eq_iff

/-- Disabled — use `mem_leftCoset_iff` and algebra instead. -/
TheoremDoc mem_leftCoset as "mem_leftCoset" in "Coset"

/-- Disabled — use `mem_leftCoset_iff` and algebra instead. -/
TheoremDoc mem_own_leftCoset as "mem_own_leftCoset" in "Coset"

/-- Disabled — prove coset equality from `leftCoset_eq_iff` instead. -/
TheoremDoc leftCoset_mem_leftCoset as "leftCoset_mem_leftCoset" in "Coset"

TheoremTab "Coset"

DisabledTactic simp group
DisabledTheorem mem_leftCoset mem_own_leftCoset leftCoset_mem_leftCoset

Statement (G : Type*) [Group G] (H : Subgroup G) (a h : G) (hh : h ∈ H) :
    a • (H : Set G) = (a * h) • (H : Set G) := by
  Hint "Reduce coset equality to subgroup membership:
  `rw [leftCoset_eq_iff]`."
  rw [leftCoset_eq_iff]
  Hint "The goal is `a⁻¹ * (a * h) ∈ H`. Cancel: `rw [inv_mul_cancel_left]`."
  rw [inv_mul_cancel_left]
  Hint (hidden := true) "`exact {hh}`."
  exact hh

Conclusion
"
Multiplying a representative by `h ∈ H` doesn't change the coset:
`aH = (ah)H`. This is because `a⁻¹(ah) = h ∈ H`.

On paper: for any `x ∈ aH`, write `x = ak` for some `k ∈ H`, then
`x = (ah)(h⁻¹k) ∈ (ah)H` since `h⁻¹k ∈ H`. The reverse is similar.

Note: `leftCoset_eq_iff` is derivable from `mem_leftCoset_iff` via
set extensionality — two cosets are equal iff they have the same
elements. We take it as given to keep the focus on using coset tools.
"
