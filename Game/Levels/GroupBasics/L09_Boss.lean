import Game.Metadata

World "GroupBasics"
Level 9

Title "Boss — Shoes and Socks Lemma"

Introduction
"
Time for the boss! In the Tutorial, you proved that
`(a * b) * (b⁻¹ * a⁻¹) = 1`. Now you'll prove the proper theorem:

`(a * b)⁻¹ = b⁻¹ * a⁻¹`

The inverse of a product is the product of the inverses in **reverse
order** — the shoes-and-socks lemma.

**Strategy**: Use `apply inv_eq_of_mul_eq_one_right` to reduce the
goal to `(a * b) * (b⁻¹ * a⁻¹) = 1`, then close it with
cancellation lemmas.
"

/-- `mul_inv_rev` says `(a * b)⁻¹ = b⁻¹ * a⁻¹` — the inverse of a
product is the product of the inverses in reverse order.

This is the **shoes-and-socks lemma**: to undo `a` then `b`, you
undo `b` first, then `a`. -/
TheoremDoc mul_inv_rev as "mul_inv_rev" in "Cancel"

NewTheorem mul_inv_rev

DisabledTactic group

TheoremTab "Cancel"

Statement (G : Type*) [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  Hint "Use `apply inv_eq_of_mul_eq_one_right` to reduce the goal
  to showing `(a * b) * (b⁻¹ * a⁻¹) = 1`."
  Hint (hidden := true) "After `apply inv_eq_of_mul_eq_one_right`, the
  goal becomes `(a * b) * (b⁻¹ * a⁻¹) = 1`. Close it with:
  `rw [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]`"
  Branch
    -- calc proof (manual)
    calc (a * b)⁻¹
        _ = (a * b)⁻¹ * 1                           := by rw [mul_one]
        _ = (a * b)⁻¹ * ((a * b) * (b⁻¹ * a⁻¹))     := by
              rw [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
        _ = b⁻¹ * a⁻¹                                := by rw [inv_mul_cancel_left]
  Branch
    -- Direct exact
    exact mul_inv_rev a b
  apply inv_eq_of_mul_eq_one_right
  Hint "The goal is now `(a * b) * (b⁻¹ * a⁻¹) = 1`. This is
  essentially the Tutorial boss. Use `mul_assoc` to re-bracket, then
  recall `mul_inv_cancel_left` from Level 4: it cancels `b * (b⁻¹ * a⁻¹)`
  down to `a⁻¹` in one step. Then `mul_inv_cancel` finishes."
  Hint (hidden := true) "If you prefer, you can also do it manually
  without `mul_inv_cancel_left`:
  `rw [mul_assoc, ← mul_assoc b b⁻¹ a⁻¹, mul_inv_cancel, one_mul, mul_inv_cancel]`"
  Branch
    -- Step by step with mul_inv_cancel_left
    rw [mul_assoc]
    Hint "Now `a * (b * (b⁻¹ * a⁻¹)) = 1`. Use `mul_inv_cancel_left`
    to cancel `b` with `b⁻¹`."
    rw [mul_inv_cancel_left]
    Hint "Now `a * a⁻¹ = 1`. This is `mul_inv_cancel`."
    rw [mul_inv_cancel]
  Branch
    -- Manual step by step (without mul_inv_cancel_left)
    rw [mul_assoc]
    rw [← mul_assoc b b⁻¹ a⁻¹]
    rw [mul_inv_cancel]
    rw [one_mul]
    rw [mul_inv_cancel]
  -- One-liner
  rw [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]

Conclusion
"
Congratulations on completing **Group Basics**!

You proved the **shoes-and-socks lemma**: `(a * b)⁻¹ = b⁻¹ * a⁻¹`.
Compare this to the Tutorial boss: there, you showed
`(a * b) * (b⁻¹ * a⁻¹) = 1` by direct calculation. Here, you used
**inverse uniqueness** to skip the direct manipulation and let the
cancellation lemmas do the heavy lifting.

**Warning**: A common mistake is to think `(a * b)⁻¹ = a⁻¹ * b⁻¹`.
This is **wrong** in general — the order reverses. In fact, the
equation `(a * b)⁻¹ = a⁻¹ * b⁻¹` is equivalent to `a * b = b * a`.
So the shoes-and-socks lemma gives you a **test for commutativity**:
a group is abelian if and only if inversion distributes without
reversing order. You'll explore this in a later world.

Your new toolkit:

| Theorem | Statement |
|---------|-----------|
| `inv_mul_cancel_left` | `a⁻¹ * (a * b) = b` |
| `mul_inv_cancel_left` | `a * (a⁻¹ * b) = b` |
| `mul_left_cancel` | `a * b = a * c → b = c` |
| `mul_right_cancel` | `a * b = c * b → a = c` |
| `inv_eq_of_mul_eq_one_right` | `a * b = 1 → a⁻¹ = b` |
| `inv_inv` | `(a⁻¹)⁻¹ = a` |
| `mul_inv_rev` | `(a * b)⁻¹ = b⁻¹ * a⁻¹` |

Two proof strategies to remember from this world:

1. **Inverse uniqueness**: to show `x⁻¹ = y`, prove `x * y = 1` and
   apply `inv_eq_of_mul_eq_one_right`. This will reappear throughout
   the course whenever you need to identify an inverse.

2. **Inside-out cancellation**: when facing a product like
   `(a * b) * (b⁻¹ * a⁻¹)`, re-bracket to bring the **inner** pair
   (`b` and `b⁻¹`) together first, cancel them, then cancel the
   **outer** pair. Work from the inside out.

In the next world, you'll practice these tools on fresh problems
with the `group` tactic available again.
"
