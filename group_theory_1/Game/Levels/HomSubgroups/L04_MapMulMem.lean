import Game.Metadata

World "HomSubgroups"
Level 4

Title "Image Products"

Introduction
"
Given `a ∈ K` and `b ∈ K`, prove that `f a * f b` is in the image
`K.map f`.

The trick: `f a * f b = f (a * b)` by `map_mul`, and `a * b ∈ K`
by subgroup closure. So the witness is `a * b`.
"

/-- Disabled — prove image membership from `mem_map` instead. -/
TheoremDoc Subgroup.mem_map_of_mem as "Subgroup.mem_map_of_mem" in "Hom"

/-- Disabled — prove image membership from `mem_map` instead. -/
TheoremDoc Subgroup.apply_coe_mem_map as "Subgroup.apply_coe_mem_map" in "Hom"

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem MulMemClass.mul_mem Subgroup.mem_map_of_mem Subgroup.apply_coe_mem_map

Statement (G H : Type*) [Group G] [Group H] (f : G →* H)
    (K : Subgroup G) (a b : G) (ha : a ∈ K) (hb : b ∈ K) :
    f a * f b ∈ K.map f := by
  Hint "The goal is `f a * f b ∈ K.map f`. The witness will be
  `a * b ∈ K`, but `f (a * b)` appears as `f a * f b` after `map_mul`.

  Rewrite first: `rw [← map_mul]`."
  Branch
    -- Alternative: go directly to mem_map and provide witness
    Hint (hidden := true) "Alternative: unfold `mem_map` and provide the
    witness directly:
    `rw [Subgroup.mem_map]; exact ⟨a * b, K.mul_mem {ha} {hb}, map_mul f a b⟩`."
    rw [Subgroup.mem_map]
    exact ⟨a * b, K.mul_mem ha hb, map_mul f a b⟩
  rw [← map_mul]
  Hint "The goal is `f (a * b) ∈ K.map f`. Now unfold `mem_map`:
  `rw [Subgroup.mem_map]`."
  rw [Subgroup.mem_map]
  Hint (hidden := true) "Provide the witness `a * b`:
  `exact ⟨a * b, K.mul_mem {ha} {hb}, rfl⟩`."
  exact ⟨a * b, K.mul_mem ha hb, rfl⟩

Conclusion
"
Image membership is harder than preimage membership: you must both
produce a witness AND verify it maps correctly.

Here, the key step was rewriting `f a * f b` as `f (a * b)` using
`← map_mul`. This made the witness obvious: `a * b`, with closure
from `K.mul_mem`.

The general pattern for image membership:
1. Simplify the target using hom properties (`← map_mul`, `← map_inv`)
2. Unfold `mem_map`
3. Provide the witness `⟨x, hx, rfl⟩`
"
