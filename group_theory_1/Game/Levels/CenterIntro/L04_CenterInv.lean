import Game.Metadata

World "CenterIntro"
Level 4

Title "Inverses of Central Elements"

Introduction
"
If `a` is in the center of `G`, is `a⁻¹` also in the center?

Yes — same **unfold-intro-algebra** pattern, then the same
**conjugation trick** from the centralizer `inv_mem` proof: insert
`a⁻¹ * a = 1` on the left, rearrange so `ha` can fire in reverse,
then cancel `a * a⁻¹` on the right.

Use a `calc` chain to transform `g * a⁻¹` into `a⁻¹ * g`.
"

TheoremTab "Center"

DisabledTactic group
DisabledTheorem InvMemClass.inv_mem

Statement (G : Type*) [Group G] (a : G)
    (ha : a ∈ Subgroup.center G) : a⁻¹ ∈ Subgroup.center G := by
  Hint "Unfold center membership: `rw [Subgroup.mem_center_iff] at ha ⊢`"
  rw [Subgroup.mem_center_iff] at ha ⊢
  Hint "Now `intro g`."
  intro g
  Hint "The goal is `g * {a}⁻¹ = {a}⁻¹ * g`. Same strategy as the
  centralizer `inv_mem` proof:

  1. Prepend `{a}⁻¹ * {a} = 1` on the left
  2. Re-associate so `{a}` is adjacent to `g`
  3. Use `← ha` to swap `{a} * g` to `g * {a}`
  4. Re-associate so `{a}` is adjacent to `{a}⁻¹`
  5. Cancel `{a} * {a}⁻¹`"
  Hint (hidden := true) "Start the `calc` block by inserting `{a}⁻¹ * {a}` on the left,
  then re-associate:
  ```
  calc g * {a}⁻¹
      = 1 * (g * {a}⁻¹)             := by rw [one_mul]
    _ = {a}⁻¹ * {a} * (g * {a}⁻¹)   := by rw [inv_mul_cancel]
    _ = {a}⁻¹ * ({a} * (g * {a}⁻¹)) := by rw [mul_assoc]
    _ = {a}⁻¹ * ({a} * g * {a}⁻¹)   := by rw [← mul_assoc {a} g]
    _ = ...
  ```
  From here, use `← ha g` to swap `{a} * g` to `g * {a}`, then
  cancel `{a} * {a}⁻¹`."
  Hint (hidden := true) "Full `calc` proof:
  ```
  calc g * {a}⁻¹
      = 1 * (g * {a}⁻¹)             := by rw [one_mul]
    _ = {a}⁻¹ * {a} * (g * {a}⁻¹)   := by rw [inv_mul_cancel]
    _ = {a}⁻¹ * ({a} * (g * {a}⁻¹)) := by rw [mul_assoc]
    _ = {a}⁻¹ * ({a} * g * {a}⁻¹)   := by rw [← mul_assoc {a} g]
    _ = {a}⁻¹ * (g * {a} * {a}⁻¹)   := by rw [← ha g]
    _ = {a}⁻¹ * (g * ({a} * {a}⁻¹)) := by rw [mul_assoc g {a}]
    _ = {a}⁻¹ * (g * 1)             := by rw [mul_inv_cancel]
    _ = {a}⁻¹ * g                   := by rw [mul_one]
  ```"
  calc g * a⁻¹
      = 1 * (g * a⁻¹)             := by rw [one_mul]
    _ = a⁻¹ * a * (g * a⁻¹)       := by rw [inv_mul_cancel]
    _ = a⁻¹ * (a * (g * a⁻¹))     := by rw [mul_assoc]
    _ = a⁻¹ * (a * g * a⁻¹)       := by rw [← mul_assoc a g]
    _ = a⁻¹ * (g * a * a⁻¹)       := by rw [← ha g]
    _ = a⁻¹ * (g * (a * a⁻¹))     := by rw [mul_assoc g a]
    _ = a⁻¹ * (g * 1)             := by rw [mul_inv_cancel]
    _ = a⁻¹ * g                   := by rw [mul_one]

Conclusion
"
This is `inv_mem` for the center. You now have all three parts of
the **membership triple** for the center:

| Property | Level | Key technique |
|----------|-------|---------------|
| `1 ∈ center G` | Level 2 | `mul_one`, `one_mul` |
| `a * b ∈ center G` | Level 3 | shuttle `g` through product |
| `a⁻¹ ∈ center G` | This level | conjugation trick |

Mathlib already knows the center is a subgroup — that's what
`Subgroup.center G` means. You just proved *why*: the three closure
properties hold because each is the same proof as the centralizer
case, but with a universal commuting hypothesis.

Notice that all three proofs followed the same **unfold-intro-algebra**
pattern from Level 2. The proofs are the same shape as the centralizer
proofs from the Subgroup Definitions world — that's no accident.
The only difference is that the commuting hypothesis went from
`hx : a * x = x * a` (specific to one element) to
`ha : ∀ g, g * a = a * g` (universal). The center IS the centralizer
of the entire group.

Note how `← mul_assoc a g` and `mul_assoc g a` used explicit
arguments to control which product gets re-associated. When `rw`
might match in multiple places, providing arguments pins the exact
occurrence.
"
