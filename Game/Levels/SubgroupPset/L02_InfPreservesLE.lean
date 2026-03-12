import Game.Metadata

World "SubgroupPset"
Level 2

Title "Intersection Preserves Containment"

Introduction
"
If `H ≤ K`, does intersecting both with `L` preserve the
containment? Prove `H ⊓ L ≤ K ⊓ L`.

Unpack the intersection, transform one component with `≤`, and
rebuild.
"

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H K L : Subgroup G)
    (hle : H ≤ K) : H ⊓ L ≤ K ⊓ L := by
  Hint "Unfold `≤` with `intro x hx`, unpack the intersection,
  apply `hle` to the `H`-component, and rebuild."
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hH, hL⟩ := hx
  rw [Subgroup.mem_inf]
  Hint (hidden := true) "`exact ⟨hle hH, hL⟩`"
  exact ⟨hle hH, hL⟩

Conclusion
"
One component changed (via `≤`) and the other stayed the same.
This is a variation of the component-wise pattern: instead of
applying the same membership lemma to both parts, you transform
one part and pass the other through unchanged.

On paper: *If `x ∈ H ∩ L`, then `x ∈ H` and `x ∈ L`. Since
`H ≤ K`, `x ∈ K`. Hence `x ∈ K` and `x ∈ L`, so `x ∈ K ∩ L`.*
"
