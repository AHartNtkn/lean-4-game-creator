import Game.Metadata

World "SubgroupBasics"
Level 8

Title "Intersection Closure"

Introduction
"
Time to combine `obtain` with the membership lemmas from the
previous world.

If `a ∈ H ⊓ K`, then `a` is in both `H` and `K`. Since both `H`
and `K` are subgroups, `a⁻¹` is in both `H` and `K` — so `a⁻¹`
should be in `H ⊓ K` too.

This is your first \"component-wise\" argument: work with each
subgroup separately, then reassemble.
"

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H K : Subgroup G)
    (a : G) (ha : a ∈ H ⊓ K) : a⁻¹ ∈ H ⊓ K := by
  Hint "First, unpack `ha` using `rw [Subgroup.mem_inf] at ha` and
  `obtain ⟨hH, hK⟩ := ha` to get `a`'s membership in each subgroup."
  rw [Subgroup.mem_inf] at ha
  obtain ⟨hH, hK⟩ := ha
  Hint "Now build `a⁻¹ ∈ H ⊓ K`. Rewrite the goal with
  `rw [Subgroup.mem_inf]` to get `a⁻¹ ∈ H ∧ a⁻¹ ∈ K`, then
  use `inv_mem` on each component."
  rw [Subgroup.mem_inf]
  Hint (hidden := true) "`exact ⟨inv_mem hH, inv_mem hK⟩`"
  exact ⟨inv_mem hH, inv_mem hK⟩

Conclusion
"
The pattern you just used will recur throughout this world and beyond:

1. **Destructure**: `obtain ⟨hH, hK⟩` from the intersection hypothesis
2. **Apply**: use a membership lemma (`inv_mem`, `mul_mem`, etc.) on
   each component separately
3. **Rebuild**: `exact ⟨..., ...⟩` to put the results back together

This is **component-wise membership**: when the carrier involves `∧`,
prove each part independently and recombine.
"
