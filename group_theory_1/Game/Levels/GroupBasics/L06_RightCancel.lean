import Game.Metadata

World "GroupBasics"
Level 6

Title "Right Cancellation Law"

Introduction
"
Here's the mirror of the left cancellation law: if `a * b = c * b`,
then `a = c`. You can cancel a common **right** factor.

The proof follows the same idea — peel off the `b` using its inverse —
but since we don't have a single convenience lemma for `(a * b) * b⁻¹ = a`
yet, you'll need to assemble the cancellation manually.

This is a **transfer exercise**: the same `rw [h]` technique from the
previous level, applied to a new surface form.
"

/-- `mul_right_cancel` says that if `a * b = c * b`, then `a = c`.

This is the **right cancellation law**: you can cancel a common right
factor in a group. Mirror of `mul_left_cancel`. -/
TheoremDoc mul_right_cancel as "mul_right_cancel" in "Cancel"

NewTheorem mul_right_cancel

DisabledTactic group

TheoremTab "Cancel"

Statement (G : Type*) [Group G] (a b c : G) (h : a * b = c * b) :
    a = c := by
  Hint "Same idea as left cancellation, but multiply by `b⁻¹` on the
  right. Each \" peel-off \" step chains three rewrites: `mul_assoc` to
  re-bracket, `mul_inv_cancel` to cancel the pair, and `mul_one` to
  clean up.

  Start a `calc` block:
  ```
  calc a = (a * b) * b⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
       _ = ...
  ```"
  Hint (hidden := true) "The full proof:
  ```
  calc a = (a * b) * b⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
       _ = (c * b) * b⁻¹ := by rw [h]
       _ = c              := by rw [mul_assoc, mul_inv_cancel, mul_one]
  ```"
  Branch
    -- Direct exact approach (for experienced players)
    exact mul_right_cancel h
  Branch
    -- Step by step (expanded calc)
    calc a = a * 1            := by rw [mul_one]
         _ = a * (b * b⁻¹)    := by rw [mul_inv_cancel]
         _ = (a * b) * b⁻¹    := by rw [← mul_assoc]
         _ = (c * b) * b⁻¹    := by rw [h]
         _ = c * (b * b⁻¹)    := by rw [mul_assoc]
         _ = c                 := by rw [mul_inv_cancel, mul_one]
  -- Compressed calc (primary)
  calc a = (a * b) * b⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
       _ = (c * b) * b⁻¹ := by rw [h]
       _ = c              := by rw [mul_assoc, mul_inv_cancel, mul_one]

Conclusion
"
Right cancellation mirrors left cancellation. Notice the asymmetry:
left cancellation used a single lemma (`inv_mul_cancel_left`), but
right cancellation required a three-step chain each time. This traces
back to the axioms — `mul_one` and `mul_inv_cancel` are right-sided,
so once we derived their left-sided counterparts (L01–L02), *left*
cancellation became easy to package. You could build
`mul_inv_cancel_right : (a * b) * b⁻¹ = a` to restore symmetry —
a natural exercise for a problem set.

Both cancellation laws are now in your toolkit.
"
