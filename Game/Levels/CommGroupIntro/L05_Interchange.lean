import Game.Metadata

World "CommGroupIntro"
Level 5

Title "The Interchange Law"

Introduction
"
In a commutative group, four factors can be rearranged freely.
One particularly useful rearrangement is the **interchange law**:

`a * b * (c * d) = a * c * (b * d)`

This swaps the inner pair `b` and `c` while keeping `a` and `d`
in place. The name **interchange law** comes from the pattern of
swapping the inner factors of a 2-by-2 grid of multiplications —
think of `(a * b) * (c * d)` as a 2x2 grid and \"interchanging\"
rows with columns to get `(a * c) * (b * d)`. The Lean name
`mul_mul_mul_comm` just says what it does: mul-mul-mul-commute.

This theorem is the key tool for the boss level, where it will
rearrange the induction step of a power-of-a-product proof.

Prove it using the commutativity tools you already have.
"

/-- `mul_mul_mul_comm` says `a * b * (c * d) = a * c * (b * d)`
in a commutative group (or commutative semigroup).

This **interchange law** swaps the inner factors `b` and `c`
while keeping `a` on the left and `d` on the right.

Useful for rearranging four-factor products. -/
TheoremDoc mul_mul_mul_comm as "mul_mul_mul_comm" in "Group"

NewTheorem mul_mul_mul_comm

TheoremTab "Group"

Statement (G : Type*) [CommGroup G] (a b c d : G) :
    a * b * (c * d) = a * c * (b * d) := by
  Hint "You need to rearrange `a * b * (c * d)` to `a * c * (b * d)`.
  The middle factors `b` and `c` need to swap.

  One approach: use `mul_assoc` to re-bracket, then `mul_left_comm`
  (from Level 2) to swap `b` past `c`, then re-bracket back.

  Or: `exact mul_mul_mul_comm a b c d` applies the theorem directly."
  Hint (hidden := true) "A step-by-step approach:
  `rw [mul_assoc, mul_assoc, mul_left_comm b c d]`

  This re-brackets to `a * (b * (c * d))` and `a * (c * (b * d))`,
  then `mul_left_comm` swaps `b` past `c`."
  Branch
    exact mul_mul_mul_comm a b c d
  Branch
    -- calc proof
    calc a * b * (c * d)
        _ = a * (b * (c * d))   := by rw [mul_assoc]
        _ = a * (c * (b * d))   := by rw [mul_left_comm b c d]
        _ = a * c * (b * d)     := by rw [← mul_assoc]
  rw [mul_assoc, mul_assoc, mul_left_comm b c d]

Conclusion
"
The interchange law `mul_mul_mul_comm` lets you swap the inner
factors of a four-element product. This is exactly the rearrangement
you'll need for the induction step of the boss.

In the next level, you'll prove that in a commutative group,
the power of a product equals the product of the powers:
`(a * b) ^ n = a ^ n * b ^ n`.
"
