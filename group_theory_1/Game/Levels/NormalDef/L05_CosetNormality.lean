import Game.Metadata

open scoped Pointwise

World "NormalDef"
Level 5

Title "Normality and Cosets"

Introduction
"
Why does normality matter? Because it makes left and right cosets agree.

Given `x ∈ aN` (the left coset), you know `x = a · n` for some `n ∈ N`.
Can you also write `x = m · a` for some `m ∈ N`? If so, then `x` is
also in the right coset `Na`.

The key: `x = an = (ana⁻¹) · a`. By normality, `ana⁻¹ ∈ N`, so
`m = ana⁻¹` works. This is why normal subgroups have equal left and
right cosets — and why coset multiplication `(aN)(bN) = (ab)N` is
well-defined only when `N` is normal.

Use `have` to store the conjugation result, then produce the witness.
"

/-- `inv_mul_cancel_right` says `a * b⁻¹ * b = a`.

This is the right-cancellation version of `inv_mul_cancel_left`.
Use it to cancel `b⁻¹ * b` on the right of an expression. -/
TheoremDoc inv_mul_cancel_right as "inv_mul_cancel_right" in "Cancel"

NewTheorem inv_mul_cancel_right

/-- Disabled — blocks the direct construction. -/
TheoremDoc eq_cosets_of_normal as "eq_cosets_of_normal" in "Normal"

TheoremTab "Normal"

DisabledTactic simp group
DisabledTheorem eq_cosets_of_normal

Statement (G : Type*) [Group G] (N : Subgroup G) (hN : N.Normal)
    (a x : G) (hx : x ∈ a • (N : Set G)) :
    ∃ m ∈ (N : Set G), x = m * a := by
  Hint "Unfold coset membership: `rw [mem_leftCoset_iff] at {hx}`.
  This gives `a⁻¹ * x ∈ N`."
  rw [mem_leftCoset_iff] at hx
  Hint "Now `{hx} : a⁻¹ * x ∈ N`. You need `m ∈ N` with `x = m * a`.
  The candidate is `m = a * (a⁻¹ * x) * a⁻¹` — the conjugate of
  `a⁻¹ * x` by `a`. Use `have` to get this into `N`:
  `have hm := hN.conj_mem (a⁻¹ * x) hx a`."
  have hm := hN.conj_mem (a⁻¹ * x) hx a
  Hint "Now `{hm} : a * (a⁻¹ * x) * a⁻¹ ∈ N`. Simplify `a * (a⁻¹ * x)`
  to `x` using `rw [mul_inv_cancel_left] at {hm}`."
  rw [mul_inv_cancel_left] at hm
  Hint "Now `{hm} : x * a⁻¹ ∈ N`. Provide the witness:
  `use x * a⁻¹, {hm}`."
  Branch
    exact ⟨x * a⁻¹, hm, (inv_mul_cancel_right x a).symm⟩
  use x * a⁻¹, hm
  Hint (hidden := true) "The goal is `x = x * a⁻¹ * a`. Use
  `rw [inv_mul_cancel_right]`."
  rw [inv_mul_cancel_right]

Conclusion
"
You proved that every element of the left coset `aN` can be written as
`m · a` for some `m ∈ N` — meaning it's also in the right coset `Na`.

This is **why normality matters**: it makes left and right cosets agree.

On paper: *If `x ∈ aN`, write `x = an` for `n ∈ N`. Then
`x = a · n = (ana⁻¹) · a`. Since `N` is normal, `ana⁻¹ ∈ N`, so
`x ∈ Na`.*

This equality `aN = Na` is exactly the condition needed to make coset
multiplication well-defined: if you pick a different representative
`a' ∈ aN`, then `a'N = aN` because `aN = Na = a'N`. Without normality,
the left and right cosets can differ, and multiplying cosets produces
different results depending on which representative you choose.
"
