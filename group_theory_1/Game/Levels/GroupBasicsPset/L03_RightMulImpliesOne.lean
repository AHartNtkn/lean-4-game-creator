import Game.Metadata

World "GroupBasicsPset"
Level 3

Title "If `a * b = b`, then `a = 1`"

Introduction
"
Mirror image: if `a * b = b`, then `a = 1`. Same idea, opposite side.
"

DisabledTactic group

TheoremTab "Cancel"

Statement (G : Type*) [Group G] (a b : G) (h : a * b = b) : a = 1 := by
  Hint "The common factor is on the *right*. Compare `a * b` with `1 * b`."
  Hint (hidden := true) "Use `apply mul_right_cancel (b := b)` to reduce
  the goal to `a * b = 1 * b`. Then `rw [h, one_mul]` closes it."
  Branch
    -- calc proof
    calc a = (a * b) * b⁻¹   := by rw [mul_assoc, mul_inv_cancel, mul_one]
         _ = b * b⁻¹         := by rw [h]
         _ = 1                := by rw [mul_inv_cancel]
  apply mul_right_cancel (b := b)
  Hint "The goal is now `a * b = 1 * b`. You have `h : a * b = b` and
  `one_mul : 1 * b = b`."
  rw [h, one_mul]

Conclusion
"
Left version used `mul_left_cancel`; right version used
`mul_right_cancel`. Together, these say that `1` is the *only* element
that leaves other elements unchanged under multiplication — in other
words, the identity element is characterized by the property `a * e = a`
(or `e * a = a`) for any `a`.

Whenever you see a common factor on one side, cancellation is the
right move.
"
