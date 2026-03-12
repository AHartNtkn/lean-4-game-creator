import Game.Metadata

World "GroupTutorial"
Level 5

Title "Associativity"

Introduction
"
The last group axiom is **associativity**: `mul_assoc` says
`(a * b) * c = a * (b * c)`.

**Important notation warning**: In Lean, `a * b * c` means `(a * b) * c`.
Multiplication is *left-associated*. So `a * b * c` and `a * (b * c)` are
**different** expressions, and you need `mul_assoc` to go between them.

In this level, the goal is `(a * b⁻¹) * b = a`. The strategy is:
1. Re-bracket with `mul_assoc` to get `a * (b⁻¹ * b)`
2. Cancel with `inv_mul_cancel`
3. Clean up with `mul_one`

This is a pattern you'll see again and again: **re-bracket, cancel, clean up**.
"

/-- `mul_assoc` says `(a * b) * c = a * (b * c)` — multiplication
in a group is associative.

Use `rw [mul_assoc]` to move parentheses rightward:
`(a * b) * c` becomes `a * (b * c)`.

Use `rw [← mul_assoc]` to move parentheses leftward:
`a * (b * c)` becomes `(a * b) * c`.

When there are multiple products, you may need to provide explicit
arguments: `rw [mul_assoc a b c]` to target a specific triple. -/
TheoremDoc mul_assoc as "mul_assoc" in "Group"

NewTheorem mul_assoc

TheoremTab "Group"

Statement (G : Type*) [Group G] (a b : G) : (a * b⁻¹) * b = a := by
  Hint "The goal is `(a * b⁻¹) * b = a`. The outer structure is
  `(_ * _) * _`, which matches `mul_assoc`. Try `rw [mul_assoc]`
  to re-bracket."
  rw [mul_assoc]
  Hint "Now you should see `a * (b⁻¹ * b) = a`. The sub-expression
  `b⁻¹ * b` matches `inv_mul_cancel`. Try `rw [inv_mul_cancel]`."
  rw [inv_mul_cancel]
  Hint "Now `a * 1 = a`. You know this one!"
  Branch
    exact mul_one a
  rw [mul_one]

Conclusion
"
You just used the **re-bracket, cancel, clean up** pattern:
1. `mul_assoc` moved the parentheses to expose `b⁻¹ * b`
2. `inv_mul_cancel` cancelled the inverse pair to `1`
3. `mul_one` removed the identity

This three-step pattern is the backbone of group algebra. In the next
level, you'll learn `calc` blocks — a structured way to write these
chains where Lean checks each step individually, so if you make a
mistake, the error points to the exact step that went wrong.

Note: `a * b * c` in Lean always means `(a * b) * c`. When you see a
product of three or more elements, the parentheses are on the **left**
by default.
"
