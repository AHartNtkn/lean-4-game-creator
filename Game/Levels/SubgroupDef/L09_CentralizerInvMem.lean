import Game.Metadata

World "SubgroupDef"
Level 9

Title "Centralizer: Closure Under Inverses"

Introduction
"
If `x` commutes with `a` (i.e., `a * x = x * a`), does `x⁻¹`
also commute with `a`?

Yes — and the proof is the most involved closure argument in this
world. The idea is to **conjugate** both sides of `hx : a * x = x * a`
by `x⁻¹`:

1. Left-multiply both sides by `x⁻¹`
2. Right-multiply both sides by `x⁻¹`
3. Cancel `x⁻¹ * x` and `x * x⁻¹` using `inv_mul_cancel` and
   `mul_inv_cancel`

The cleanest approach is a `calc` chain that transforms
`a * x⁻¹` step by step into `x⁻¹ * a`.
"

TheoremTab "Group"

Statement (G : Type*) [Group G] (a x : G)
    (hx : a * x = x * a) : a * x⁻¹ = x⁻¹ * a := by
  Hint "The goal is `a * x⁻¹ = x⁻¹ * a`. You have `hx : a * x = x * a`.

  **Strategy**: Start from `a * x⁻¹`, insert `x⁻¹ * x` on the left
  (which equals `1`), rearrange so `hx` can fire in reverse, then
  cancel `x * x⁻¹` on the right.

  Try a `calc` block:
  ```
  calc a * x⁻¹
      = 1 * (a * x⁻¹)             := by rw [one_mul]
    _ = x⁻¹ * x * (a * x⁻¹)       := by rw [inv_mul_cancel]
    _ = ...
  ```"
  Hint (hidden := true) "**Step-by-step plan**: After prepending `x⁻¹ * x`
  on the left, re-associate so that `x` is adjacent to `a`, giving
  `x * a`. Then use `← hx` to replace `x * a` with `a * x`. Now
  re-associate so `x` is adjacent to `x⁻¹`, and cancel `x * x⁻¹`
  using `mul_inv_cancel`. Finally simplify `a * 1` to `a` with
  `mul_one`."
  Hint (hidden := true) "The full `calc` proof:
  ```
  calc a * x⁻¹
      = 1 * (a * x⁻¹)             := by rw [one_mul]
    _ = x⁻¹ * x * (a * x⁻¹)       := by rw [inv_mul_cancel]
    _ = x⁻¹ * (x * (a * x⁻¹))     := by rw [mul_assoc]
    _ = x⁻¹ * (x * a * x⁻¹)       := by rw [← mul_assoc x a]
    _ = x⁻¹ * (a * x * x⁻¹)       := by rw [← hx]
    _ = x⁻¹ * (a * (x * x⁻¹))     := by rw [mul_assoc a x]
    _ = x⁻¹ * (a * 1)             := by rw [mul_inv_cancel]
    _ = x⁻¹ * a                   := by rw [mul_one]
  ```"
  calc a * x⁻¹
      = 1 * (a * x⁻¹)             := by rw [one_mul]
    _ = x⁻¹ * x * (a * x⁻¹)       := by rw [inv_mul_cancel]
    _ = x⁻¹ * (x * (a * x⁻¹))     := by rw [mul_assoc]
    _ = x⁻¹ * (x * a * x⁻¹)       := by rw [← mul_assoc x a]
    _ = x⁻¹ * (a * x * x⁻¹)       := by rw [← hx]
    _ = x⁻¹ * (a * (x * x⁻¹))     := by rw [mul_assoc a x]
    _ = x⁻¹ * (a * 1)             := by rw [mul_inv_cancel]
    _ = x⁻¹ * a                   := by rw [mul_one]

Conclusion
"
The inverse closure proof is the most involved of the three, but
the strategy is clean: sandwich `a * x⁻¹` between `x⁻¹ * x` on
the left and `x * x⁻¹` on the right, use `hx` (in reverse) to
swap `x * a` back to `a * x`, then cancel the flanking pairs.

You've now proved all three closure properties for the centralizer
separately:

| Property | Proved |
|----------|--------|
| `one_mem'` | Level 5 (`a * 1 = 1 * a` via `mul_one`, `one_mul`) |
| `mul_mem'` | Level 8 (shuttle `a` through `x * y`) |
| `inv_mem'` | This level (conjugate by `x⁻¹`) |

In the boss level, you'll combine all three into a single subgroup
construction. But first, a retrieval exercise to solidify the
subgroup construction pattern.
"
