import Game.Metadata

World "GroupBasics"
Level 3

Title "Left Inverse Cancellation"

Introduction
"
In the Tutorial, you proved `a⁻¹ * (a * b) = b` as a calc exercise.
Now let's add it to your toolkit as a proper lemma:
`inv_mul_cancel_left`.

This is the **left inverse cancellation** law: multiplying by `a⁻¹`
on the left undoes multiplication by `a`.

The proof is the same re-bracket / cancel / clean up pattern from
the Tutorial.
"

/-- `inv_mul_cancel_left` says `a⁻¹ * (a * b) = b`.

Use it with `rw [inv_mul_cancel_left]` to cancel a left inverse pair.
This is faster than the three-step re-bracket / cancel / clean up
pattern — it does all three at once. -/
TheoremDoc inv_mul_cancel_left as "inv_mul_cancel_left" in "Cancel"

NewTheorem inv_mul_cancel_left

DisabledTactic group

TheoremTab "Cancel"

Statement (G : Type*) [Group G] (a b : G) : a⁻¹ * (a * b) = b := by
  Hint "This is the re-bracket / cancel / clean up pattern:
  1. `rw [← mul_assoc]` to get `(a⁻¹ * a) * b`
  2. `rw [inv_mul_cancel]` to get `1 * b`
  3. `rw [one_mul]` to get `b`"
  Branch
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  rw [← mul_assoc]
  Hint "Now you see `(a⁻¹ * a) * b = b`. Cancel the inverse pair."
  rw [inv_mul_cancel]
  Hint "Now `1 * b = b`. Clean up."
  rw [one_mul]

Conclusion
"
You've packaged the three-step pattern into one lemma. From now on,
`rw [inv_mul_cancel_left]` does all three rewrites at once: re-bracket,
cancel, clean up.
"
