import Game.Metadata

World "SubgroupDef"
Level 11

Title "Boss — The Centralizer Subgroup"

Introduction
"
The **centralizer** of an element `a` in a group `G` is the set of
all elements that commute with `a`:

`{g : G | a * g = g * a}`

You've already proved each closure property individually. Now put
them all together: use `apply Subgroup.mk_carrier` to build a
subgroup with this specific carrier, and prove each obligation
using `intro`, `show`, and the techniques from Levels 5, 8, and 9.

Your toolkit for this level:

| Theorem | Statement |
|---------|-----------|
| `mul_assoc` | `a * b * c = a * (b * c)` |
| `mul_one` | `a * 1 = a` |
| `one_mul` | `1 * a = a` |
| `mul_inv_cancel` | `a * a⁻¹ = 1` |
| `inv_mul_cancel` | `a⁻¹ * a = 1` |
| `inv_one` | `(1 : G)⁻¹ = 1` |
"

TheoremTab "Group"

Statement (G : Type*) [Group G] (a : G) :
    ∃ H : Subgroup G, H.carrier = {g : G | a * g = g * a} := by
  Hint "Start with `apply Subgroup.mk_carrier` to set up the three
  closure obligations."
  apply Subgroup.mk_carrier
  · Hint "**mul_mem**: Show the product of two commuting elements
    also commutes with `{a}`.

    Start with `intro x y hx hy`."
    intro x y hx hy
    Hint "Use `show {a} * ({x} * {y}) = {x} * {y} * {a}` to unfold
    membership, then shuttle `{a}` through `{x} * {y}` using
    `hx` and `hy`. Same proof as Level 8."
    show a * (x * y) = x * y * a
    Hint (hidden := true) "`rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]`"
    rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]
  · Hint "**one_mem**: `1` commutes with `{a}`.

    `show {a} * 1 = 1 * {a}` then `rw [mul_one, one_mul]`."
    show a * 1 = 1 * a
    rw [mul_one, one_mul]
  · Hint "**inv_mem**: If an element commutes with `{a}`, its
    inverse does too.

    `intro x hx` to get the element and hypothesis."
    intro x hx
    Hint "Use `show {a} * {x}⁻¹ = {x}⁻¹ * {a}` and the `calc`
    proof from Level 9."
    show a * x⁻¹ = x⁻¹ * a
    Hint (hidden := true) "Start from `{a} * {x}⁻¹`, insert
    `{x}⁻¹ * {x}` on the left (which is `1`), rearrange using
    `mul_assoc`, apply `← hx` to swap `{x} * {a}` to `{a} * {x}`,
    then cancel `{x} * {x}⁻¹` on the right."
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
Congratulations on completing **Subgroup Definitions**!

You built the **centralizer** of an element as a subgroup — from
scratch, verifying all three closure properties by hand:

| Property | Proof technique |
|----------|----------------|
| `one_mem` | `mul_one` and `one_mul` |
| `mul_mem` | Shuttle `a` through the product using `hx`, `hy` |
| `inv_mem` | Conjugate by `x⁻¹`, use `hx` in reverse, cancel |

This three-part pattern — prove closure under identity, multiplication,
and inverse — is called the **membership triple**. You'll use it every
time you need to show a set is a subgroup.

The centralizer of `a` measures how \"commutative\" `a` is:
- If `a` commutes with every element, the centralizer is all of `G`
  — this happens when `a` is in the **center** of `G`.
- If `a` commutes with nothing but itself and `1`, the centralizer
  is small.
- The centralizer is always a subgroup, as you just proved.

Your new tools from this world:

| Item | Type |
|------|------|
| `Subgroup G` | Definition |
| `one_mem H` | `1 ∈ H` |
| `mul_mem` | `x ∈ H → y ∈ H → x * y ∈ H` |
| `inv_mem` | `x ∈ H → x⁻¹ ∈ H` |
| `inv_one` | `(1 : G)⁻¹ = 1` |
| `Subgroup.mk_carrier` | Build a subgroup with specified carrier |
| `show` | Tactic: replace goal with definitionally equal form |
| `intro` | Tactic: introduce hypotheses |
| `rfl` | Tactic: prove `x = x` |

Now that you can build subgroups, the next question is: how do
subgroups relate to each other? In the next world, you'll explore
the subgroup lattice.
"
