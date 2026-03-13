import Game.Metadata

World "GroupBasicsPset"
Level 7

Title "Boss — Triple Shoes and Socks"

Introduction
"
The shoes-and-socks lemma says `(a * b)⁻¹ = b⁻¹ * a⁻¹`. What happens
with three factors?

Prove that `(a * b * c)⁻¹ = c⁻¹ * b⁻¹ * a⁻¹`.

The `group` tactic is disabled. Work it out by hand.
"

DisabledTactic group

TheoremTab "Cancel"

Statement (G : Type*) [Group G] (a b c : G) :
    (a * b * c)⁻¹ = c⁻¹ * b⁻¹ * a⁻¹ := by
  Hint "You proved `(a * b)⁻¹ = b⁻¹ * a⁻¹` in Group Basics. That was
  `mul_inv_rev`. Can you apply it *twice* to handle three factors?"
  Hint (hidden := true) "Apply `mul_inv_rev` to `((a * b) * c)⁻¹` to get
  `c⁻¹ * (a * b)⁻¹`. Then apply `mul_inv_rev` again to `(a * b)⁻¹`.
  After these two rewrites the goal is `c⁻¹ * (b⁻¹ * a⁻¹) = c⁻¹ * b⁻¹ * a⁻¹`.
  Use `← mul_assoc` to re-bracket the left side to match."
  Branch
    -- calc proof
    calc (a * b * c)⁻¹
        _ = c⁻¹ * (a * b)⁻¹     := by rw [mul_inv_rev]
        _ = c⁻¹ * (b⁻¹ * a⁻¹)   := by rw [mul_inv_rev]
        _ = c⁻¹ * b⁻¹ * a⁻¹     := by rw [← mul_assoc]
  rw [mul_inv_rev, mul_inv_rev, ← mul_assoc]

Conclusion
"
Congratulations on completing the **Group Basics Problem Set**!

The triple shoes-and-socks lemma follows from applying the two-factor
version twice, then fixing the brackets. This is a general pattern:
`mul_inv_rev` is the inductive step, and you can extend it to any
number of factors.

Notice that the reversal gets more dramatic as you add factors. In a
**commutative** group, the reversal disappears entirely:
`(a * b * c)⁻¹ = a⁻¹ * b⁻¹ * c⁻¹`. Whether a group has this
simplification is one of the central questions you'll explore next.

You've now practiced the core group theory toolkit on fresh problems:
cancellation laws, inverse uniqueness, inverse injectivity,
shoes-and-socks, and double inverse. These moves will appear
throughout the course.
"
