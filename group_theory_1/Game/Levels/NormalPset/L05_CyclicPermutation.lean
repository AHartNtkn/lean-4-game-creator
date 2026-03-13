import Game.Metadata

World "NormalPset"
Level 5

Title "Cyclic Permutation"

Introduction
"
From `a * b * c ∈ N`, can you derive `c * a * b ∈ N`?

In a normal subgroup, you can cyclically permute the factors of a
product while staying in `N`. The key is choosing the right
conjugator: conjugating `a * b * c` by `a * b` (via `conj_mem'`)
moves `a * b` from the left to the right.

This is the **strategic conjugator** pattern from the lecture —
now with reduced scaffolding.
"

TheoremTab "Normal"

DisabledTactic simp group

Statement (G : Type*) [Group G] (N : Subgroup G) (hN : N.Normal)
    (a b c : G) (h : a * b * c ∈ N) : c * a * b ∈ N := by
  Hint "Conjugate `a * b * c` to move `a * b` from the left to the
  right. The conjugator `a * b` does this via `conj_mem'`:
  `have h' := hN.conj_mem' (a * b * c) h (a * b)`."
  Branch
    have h' := hN.conj_mem (a * b * c) h (a * b)⁻¹
    Hint "Clean up:
    `rw [inv_mul_cancel_left, inv_inv, ← mul_assoc] at {h'}`."
    rw [inv_mul_cancel_left, inv_inv, ← mul_assoc] at h'
    exact h'
  have h' := hN.conj_mem' (a * b * c) h (a * b)
  Hint "Now `{h'} : (a * b)⁻¹ * (a * b * c) * (a * b) ∈ N`.
  Cancel `(a * b)⁻¹ * (a * b)` on the left:
  `rw [inv_mul_cancel_left] at {h'}`.
  Then fix associativity: `rw [← mul_assoc] at {h'}`."
  rw [inv_mul_cancel_left, ← mul_assoc] at h'
  Hint (hidden := true) "`exact {h'}`."
  exact h'

Conclusion
"
**Cyclic permutation**: in a normal subgroup, `abc ∈ N` implies
`cab ∈ N` (and `bca ∈ N` by applying the trick again).

The proof uses the **strategic conjugator** pattern: choose a
conjugator that rearranges the product. Here, conjugating by `a * b`
shifts it from the left to the right.

On paper: *Since `abc ∈ N` and `N` is normal, conjugate by `ab`:
`(ab)⁻¹(abc)(ab) = c(ab) ∈ N`.*

This is the same \"conjugate-then-cancel\" technique from the lecture,
applied to a three-element product instead of two.
"
