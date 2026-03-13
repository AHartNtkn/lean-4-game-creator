import Game.Metadata

World "GroupTutorial"
Level 4

Title "Left Inverse"

Introduction
"
The theorem `inv_mul_cancel` says that `a⁻¹ * a = 1` — the inverse
cancels on the **left** too.

Together with `mul_inv_cancel` (which says `a * a⁻¹ = 1`), you now
have cancellation in both directions.

The naming convention continues: `mul_inv_cancel` has the inverse on the
**right** (`a * a⁻¹`), while `inv_mul_cancel` has the inverse on the
**left** (`a⁻¹ * a`).
"

/-- `inv_mul_cancel` says `a⁻¹ * a = 1` for any element `a` of a group.

Use it with `rw [inv_mul_cancel]` when you see `_⁻¹ * _` where
both sides are the same element.

Don't confuse with `mul_inv_cancel`, which handles `a * a⁻¹`. -/
TheoremDoc inv_mul_cancel as "inv_mul_cancel" in "Group"

NewTheorem inv_mul_cancel

TheoremTab "Group"

Statement (G : Type*) [Group G] (a b : G) : b * (a⁻¹ * a) = b := by
  Hint "The goal is `b * (a⁻¹ * a) = b`. Inside the parentheses,
  you see `a⁻¹ * a`. Which axiom handles the inverse on the left?"
  Branch
    rw [inv_mul_cancel, mul_one]
  rw [inv_mul_cancel]
  Hint "Now you should see `b * 1 = b`. You've seen this before!"
  Branch
    exact mul_one b
  rw [mul_one]

Conclusion
"
You now have both cancellation laws:
- `mul_inv_cancel`: `a * a⁻¹ = 1`
- `inv_mul_cancel`: `a⁻¹ * a = 1`

(Like `one_mul`, `inv_mul_cancel` is derivable from the other axioms.
The proof is a satisfying exercise — you'll do it in the next world.)

Together with `mul_one` and `one_mul`, you can insert or remove identity
elements and cancel inverse pairs. There's one more axiom to go:
**associativity**.
"
