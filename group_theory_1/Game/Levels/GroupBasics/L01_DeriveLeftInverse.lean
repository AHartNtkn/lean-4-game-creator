import Game.Metadata

World "GroupBasics"
Level 1

Title "Deriving Left Inverse"

Introduction
"
The Group Tutorial presented five tools as if they were all on equal
footing. In fact, only three are axioms:

- `mul_assoc`: $(a * b) * c = a * (b * c)$
- `mul_one`: $a * 1 = a$
- `mul_inv_cancel`: $a * a^{-1} = 1$

The other two — `inv_mul_cancel` and `one_mul` — are *consequences*
of these three. In this level, you'll derive `inv_mul_cancel`
($a^{-1} * a = 1$) from scratch.

This is a longer proof than anything in the Tutorial — seven rewrite
steps. The strategy is to introduce `(a⁻¹)⁻¹` as a catalyst:

1. Pad the right side with `* 1`
2. Replace `1` with `a⁻¹ * (a⁻¹)⁻¹` using `mul_inv_cancel`
3. Re-bracket to bring `a` next to `a⁻¹`
4. Cancel `a * a⁻¹`
5. Clean up

The `inv_mul_cancel` theorem is **disabled** for this level — you
can't use it until you've proved it.
"

/-- `inv_mul_cancel` says `a⁻¹ * a = 1` — disabled for this level
because you are deriving it from the other axioms. -/
TheoremDoc inv_mul_cancel as "inv_mul_cancel" in "Group"

DisabledTheorem inv_mul_cancel
DisabledTactic group

TheoremTab "Group"

Statement (G : Type*) [Group G] (a : G) : a⁻¹ * a = 1 := by
  Hint "This is a derivation — you're proving something the Tutorial
  gave you for free. The proof is long but each step is a single rewrite
  you already know.

  Start a `calc` block. The first step introduces `* 1` on the right:
  `_ = (a⁻¹ * a) * 1 := by rw [mul_one]`"
  Hint (hidden := true) "After `_ = (a⁻¹ * a) * 1`, replace the `1`
  with `a⁻¹ * (a⁻¹)⁻¹` using `mul_inv_cancel`, then re-bracket:
  ```
  calc a⁻¹ * a
      _ = (a⁻¹ * a) * 1                       := by rw [mul_one]
      _ = (a⁻¹ * a) * (a⁻¹ * (a⁻¹)⁻¹)         := by rw [mul_inv_cancel]
      _ = ((a⁻¹ * a) * a⁻¹) * (a⁻¹)⁻¹         := by rw [← mul_assoc]
      ...
  ```
  The remaining steps bring `a` next to `a⁻¹`, cancel them, and clean up."
  Hint (hidden := true) "Here is the full calc block:
  ```
  calc a⁻¹ * a
      _ = (a⁻¹ * a) * 1                       := by rw [mul_one]
      _ = (a⁻¹ * a) * (a⁻¹ * (a⁻¹)⁻¹)         := by rw [mul_inv_cancel]
      _ = ((a⁻¹ * a) * a⁻¹) * (a⁻¹)⁻¹         := by rw [← mul_assoc]
      _ = (a⁻¹ * (a * a⁻¹)) * (a⁻¹)⁻¹         := by rw [mul_assoc a⁻¹ a a⁻¹]
      _ = (a⁻¹ * 1) * (a⁻¹)⁻¹                 := by rw [mul_inv_cancel]
      _ = a⁻¹ * (a⁻¹)⁻¹                        := by rw [mul_one]
      _ = 1                                     := by rw [mul_inv_cancel]
  ```
  Each step uses a **forward** `rw` that simplifies the right-hand side
  to match the left-hand side."
  calc a⁻¹ * a
      _ = (a⁻¹ * a) * 1                       := by rw [mul_one]
      _ = (a⁻¹ * a) * (a⁻¹ * (a⁻¹)⁻¹)         := by rw [mul_inv_cancel]
      _ = ((a⁻¹ * a) * a⁻¹) * (a⁻¹)⁻¹         := by rw [← mul_assoc]
      _ = (a⁻¹ * (a * a⁻¹)) * (a⁻¹)⁻¹         := by rw [mul_assoc a⁻¹ a a⁻¹]
      _ = (a⁻¹ * 1) * (a⁻¹)⁻¹                 := by rw [mul_inv_cancel]
      _ = a⁻¹ * (a⁻¹)⁻¹                        := by rw [mul_one]
      _ = 1                                     := by rw [mul_inv_cancel]

Conclusion
"
You just derived `inv_mul_cancel` from `mul_assoc`, `mul_one`, and
`mul_inv_cancel` alone. The trick was introducing `(a⁻¹)⁻¹` as a
catalyst — it appeared temporarily and cancelled away, leaving the
result we wanted.

This is why mathematicians say there are only **three** group axioms.
Everything else is a theorem.
"
