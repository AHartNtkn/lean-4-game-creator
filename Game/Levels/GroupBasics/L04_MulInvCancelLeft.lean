import Game.Metadata

World "GroupBasics"
Level 4

Title "Right Inverse Cancellation"

Introduction
"
Here's the mirror image: `mul_inv_cancel_left` says `a * (a⁻¹ * b) = b`.

Multiplying by `a` on the left undoes multiplication by `a⁻¹`. The proof
uses the same three-step pattern, but with `mul_inv_cancel` instead of
`inv_mul_cancel`.
"

/-- `mul_inv_cancel_left` says `a * (a⁻¹ * b) = b`.

Use it with `rw [mul_inv_cancel_left]` to cancel an element with its
inverse on the left. Mirror of `inv_mul_cancel_left`. -/
TheoremDoc mul_inv_cancel_left as "mul_inv_cancel_left" in "Cancel"

NewTheorem mul_inv_cancel_left

DisabledTactic group

TheoremTab "Cancel"

Statement (G : Type*) [Group G] (a b : G) : a * (a⁻¹ * b) = b := by
  Hint "Same three-step pattern as the previous level, but with
  `mul_inv_cancel` instead of `inv_mul_cancel`:
  1. Re-bracket with `← mul_assoc`
  2. Cancel the inverse pair
  3. Clean up the identity"
  Hint (hidden := true) "The full chain:
  `rw [← mul_assoc, mul_inv_cancel, one_mul]`"
  Branch
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  rw [← mul_assoc]
  Hint "Now `(a * a⁻¹) * b = b`. Cancel with `mul_inv_cancel`."
  rw [mul_inv_cancel]
  rw [one_mul]

Conclusion
"
You now have a matched pair of cancellation lemmas:
- `inv_mul_cancel_left`: `a⁻¹ * (a * b) = b`
- `mul_inv_cancel_left`: `a * (a⁻¹ * b) = b`

These are much more convenient than the raw three-step pattern.
Keep both in mind — `mul_inv_cancel_left` will be essential for the
boss level, where you'll need to simplify expressions like
`b * (b⁻¹ * ...)`.

In the next level, you'll use them to prove a proper cancellation law.
"
