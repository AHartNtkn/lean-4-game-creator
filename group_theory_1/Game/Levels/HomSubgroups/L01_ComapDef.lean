import Game.Metadata

World "HomSubgroups"
Level 1

Title "Preimage of a Subgroup"

Introduction
"
If `f : G →* H` is a homomorphism and `K` is a subgroup of `H`, the
**preimage** `f⁻¹(K) = {x ∈ G | f(x) ∈ K}` is a subgroup of `G`.

Lean calls this `Subgroup.comap f K` (\"contravariant map\" — it goes
backward, from `H` to `G`).

The unfolding lemma is:

`Subgroup.mem_comap : x ∈ K.comap f ↔ f x ∈ K`

Prove that `1` is always in the preimage.
"

/-- The preimage of a subgroup `K` under a group homomorphism `f`.

`Subgroup.comap f K` is the subgroup `{x ∈ G | f x ∈ K}`.

Use `rw [Subgroup.mem_comap]` to convert between `x ∈ K.comap f`
and `f x ∈ K`. -/
DefinitionDoc Subgroup.comap as "Subgroup.comap"

NewDefinition Subgroup.comap

/-- `Subgroup.mem_comap` says: for a group homomorphism `f : G →* H`
and a subgroup `K` of `H`,

`x ∈ K.comap f ↔ f x ∈ K`

Use `rw [Subgroup.mem_comap]` to unfold preimage membership. -/
TheoremDoc Subgroup.mem_comap as "Subgroup.mem_comap" in "Hom"

NewTheorem Subgroup.mem_comap

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem OneMemClass.one_mem

Statement (G H : Type*) [Group G] [Group H] (f : G →* H)
    (K : Subgroup H) : (1 : G) ∈ K.comap f := by
  Hint "The goal is `1 ∈ K.comap f`. Unfold preimage membership:
  `rw [Subgroup.mem_comap]`."
  rw [Subgroup.mem_comap]
  Hint "The goal is `f 1 ∈ K`. Use the hom property `map_one`
  to simplify: `rw [map_one]`."
  rw [map_one]
  Hint (hidden := true) "The goal is `1 ∈ K`. Use `exact K.one_mem`."
  exact K.one_mem

Conclusion
"
The move: unfold `mem_comap`, apply a hom property, close with
subgroup closure. This is the **hom-through-comap** pattern:

1. `rw [Subgroup.mem_comap]` — reduce to membership in `K`
2. Apply hom properties (`map_one`, `map_mul`, `map_inv`)
3. Close with subgroup closure (`K.one_mem`, `K.mul_mem`, `K.inv_mem`)

This same pattern works for showing `comap f K` is closed under
multiplication and inverses — you'll prove the multiplication case
next.
"
