import Game.Metadata

World "SubgroupDef"
Level 8

Title "Centralizer: Closure Under Multiplication"

Introduction
"
Given an element `a` of a group `G`, the **centralizer** of `a` is
the set of all elements that commute with `a`:

`{g : G | a * g = g * a}`

This set is important throughout group theory — it measures how far
`a` is from being \"central\" (commuting with everything).

Is this set a subgroup? To find out, you need to verify the three
closure properties. In this level, you'll prove **closure under
multiplication**: if `x` and `y` both commute with `a`, then `x * y`
commutes with `a` too.

The proof is an `rw` chain using `mul_assoc` and the hypotheses
`hx : a * x = x * a` and `hy : a * y = y * a`.
"

TheoremTab "Group"

Statement (G : Type*) [Group G] (a x y : G)
    (hx : a * x = x * a) (hy : a * y = y * a) :
    a * (x * y) = x * y * a := by
  Hint "You need to show `a * (x * y) = x * y * a`.

  The idea: move `a` through `x` using `hx`, then through `y`
  using `hy`. The `mul_assoc` rewrites handle the brackets.

  **Plan**:
  1. `← mul_assoc` to get `a * x * y`
  2. `hx` to replace `a * x` with `x * a`
  3. `mul_assoc` to get `x * (a * y)`
  4. `hy` to replace `a * y` with `y * a`
  5. `← mul_assoc` to get `x * y * a`"
  Hint (hidden := true) "`rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]`"
  Branch
    Hint (hidden := true) "You can also use a `calc` block. Start with
    `calc a * ({x} * {y})` and shuttle `a` through one factor at a time:
    ```
    calc a * ({x} * {y})
        = a * {x} * {y}     := by rw [mul_assoc]
      _ = {x} * a * {y}     := by rw [hx]
      _ = {x} * (a * {y})   := by rw [← mul_assoc]
      _ = {x} * ({y} * a)   := by rw [hy]
      _ = {x} * {y} * a     := by rw [mul_assoc]
    ```"
    calc a * (x * y)
        = a * x * y     := by rw [mul_assoc]
      _ = x * a * y     := by rw [hx]
      _ = x * (a * y)   := by rw [← mul_assoc]
      _ = x * (y * a)   := by rw [hy]
      _ = x * y * a     := by rw [mul_assoc]
  rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]

Conclusion
"
The multiplication closure proof shuttles `a` from left to right
through the product `x * y`, using `hx` and `hy` one at a time.
Each use of `mul_assoc` re-brackets so the next hypothesis applies.

This is a common pattern in centralizer proofs: you move the fixed
element through one factor at a time.

Next: closure under inverses — the hardest of the three.
"
