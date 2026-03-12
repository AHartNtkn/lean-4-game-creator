import Game.Metadata

World "SubgroupDef"
Level 4

Title "Combining Membership Lemmas"

Introduction
"
Now combine the three membership lemmas. Given `a ∈ H` and `b ∈ H`,
prove that `a * b⁻¹ ∈ H`.

This requires two steps: first get `b⁻¹ ∈ H` from `inv_mem`, then
combine with `a ∈ H` using `mul_mem`.
"

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H : Subgroup G) (a b : G)
    (ha : a ∈ H) (hb : b ∈ H) : a * b⁻¹ ∈ H := by
  Hint "The goal is `a * b⁻¹ ∈ H`. This is a product, so `mul_mem`
  applies — but you need `a ∈ H` (which you have) and `b⁻¹ ∈ H`
  (which follows from `inv_mem hb`).

  Try `exact mul_mem ha (inv_mem hb)`."
  Hint (hidden := true) "Alternatively, use `apply mul_mem` to split
  the goal into `a ∈ H` and `b⁻¹ ∈ H`, then close each one."
  Branch
    apply mul_mem
    · exact ha
    · exact inv_mem hb
  exact mul_mem ha (inv_mem hb)

Conclusion
"
You chained `mul_mem` and `inv_mem` together. In fact, closure under
`x * y⁻¹` is an equivalent characterization of subgroups: a
nonempty subset `H` is a subgroup if and only if `x * y⁻¹ ∈ H`
whenever `x, y ∈ H`. This is sometimes called the **one-step
subgroup test**.

The fact that `mul_mem`, `inv_mem`, and `one_mem` compose naturally
is what makes subgroup proofs work. You'll use this kind of
composition constantly.
"
