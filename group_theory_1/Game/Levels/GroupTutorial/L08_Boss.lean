import Game.Metadata

World "GroupTutorial"
Level 8

Title "The Boss — Shoes and Socks"

Introduction
"
Time for the boss level! You must prove that

`(a * b) * (b⁻¹ * a⁻¹) = 1`

using only the five group axioms and `calc`. The `group` tactic is
**disabled** for this level — you need to do this by hand.

This is the **shoes and socks** principle: to undo putting on socks
then shoes, you take off shoes first, then socks. The \"inverse\" of
doing `a` then `b` is undoing `b` then undoing `a`.

**Strategy**: cancel from the inside out. Use `mul_assoc` to strip the
outer parentheses, then use targeted `← mul_assoc` to isolate `b * b⁻¹`
in the middle. After canceling that, `a * a⁻¹` remains.

Use a `calc` block to show each step.
"

DisabledTactic group

TheoremTab "Group"

Statement (G : Type*) [Group G] (a b : G) : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
  Hint "This is your first boss. Plan your proof before writing it.
  The strategy: cancel `b * b⁻¹` from the inside, then cancel `a * a⁻¹`.

  Use a `calc` block or an `rw` chain — your choice."
  Hint (hidden := true) "Here is the plan, step by step:
  ```
  (a * b) * (b⁻¹ * a⁻¹)
  = a * (b * (b⁻¹ * a⁻¹))    -- mul_assoc
  = a * ((b * b⁻¹) * a⁻¹)    -- ← mul_assoc b b⁻¹ a⁻¹
  = a * (1 * a⁻¹)             -- mul_inv_cancel
  = a * a⁻¹                   -- one_mul
  = 1                          -- mul_inv_cancel
  ```
  Try writing this as a `calc` block or as
  `rw [mul_assoc, ← mul_assoc b b⁻¹ a⁻¹, mul_inv_cancel, one_mul, mul_inv_cancel]`."
  Branch
    -- rw chain path (step by step)
    rw [mul_assoc]
    Hint "Good, you have `a * (b * (b⁻¹ * a⁻¹)) = 1`. Now re-bracket
    the inner expression: use `rw [← mul_assoc b b⁻¹ a⁻¹]` to get
    `(b * b⁻¹) * a⁻¹`."
    rw [← mul_assoc b b⁻¹ a⁻¹]
    Hint "Now you should see `a * ((b * b⁻¹) * a⁻¹) = 1`. Cancel
    `b * b⁻¹` with `mul_inv_cancel`."
    rw [mul_inv_cancel]
    Hint "Now `a * (1 * a⁻¹) = 1`. Use `one_mul` to simplify."
    rw [one_mul]
    Hint "Now `a * a⁻¹ = 1`. This is `mul_inv_cancel`."
    rw [mul_inv_cancel]
  Branch
    -- rw chain one-liner (full explicit args)
    rw [mul_assoc, ← mul_assoc b b⁻¹ a⁻¹, mul_inv_cancel, one_mul, mul_inv_cancel]
  -- calc proof path (primary)
  calc (a * b) * (b⁻¹ * a⁻¹)
      _ = a * (b * (b⁻¹ * a⁻¹))   := by rw [mul_assoc]
      _ = a * ((b * b⁻¹) * a⁻¹)   := by
            Hint "Re-bracket the inner expression to expose `b * b⁻¹`.
            Use `rw [← mul_assoc b b⁻¹ a⁻¹]` — the explicit arguments
            tell Lean which triple to target."
            rw [← mul_assoc b b⁻¹ a⁻¹]
      _ = a * (1 * a⁻¹)           := by
            Hint "Cancel `b * b⁻¹` with `mul_inv_cancel`."
            rw [mul_inv_cancel]
      _ = a * a⁻¹                 := by
            Hint "Simplify `1 * a⁻¹` to `a⁻¹` with `one_mul`."
            rw [one_mul]
      _ = 1                        := by
            Hint "This is `mul_inv_cancel`."
            rw [mul_inv_cancel]

Conclusion
"
Congratulations on completing the **Group Tutorial**!

You proved that `(a * b) * (b⁻¹ * a⁻¹) = 1` — the **shoes and socks**
principle. In words: we re-bracketed to bring `b` next to `b⁻¹`,
cancelled them to `1`, cleaned up the identity, then cancelled `a`
with `a⁻¹`.

The general strategy: when multiple inverse pairs need to cancel,
**work from the inside out** — re-bracket to expose and cancel the
innermost pair first, then work outward. You'll use this pattern often.

You now have five axioms and two proof tools in your toolkit:

| Axiom | Statement |
|---|---|
| `mul_assoc` | `(a * b) * c = a * (b * c)` |
| `mul_one` | `a * 1 = a` |
| `one_mul` | `1 * a = a` |
| `mul_inv_cancel` | `a * a⁻¹ = 1` |
| `inv_mul_cancel` | `a⁻¹ * a = 1` |

**Tools**: `calc` blocks for step-by-step proofs, and the `group` tactic
for automatic solutions (when it's not disabled!).

In the next world, we'll use these axioms to **derive** new theorems:
cancellation laws, uniqueness of inverses, and the shoes-and-socks
lemma as a proper theorem. In fact, the result you just proved is
exactly the key ingredient for showing that `(a * b)⁻¹ = b⁻¹ * a⁻¹` —
the W2 boss.
"
