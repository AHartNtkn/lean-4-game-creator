import Game.Metadata

World "SubgroupBasics"
Level 10

Title "Intersection Is Commutative"

Introduction
"
Prove that `H ⊓ K = K ⊓ H` — intersection doesn't depend on the
order.

This is a retrieval exercise: use `ext`, then `refine ⟨?_, ?_⟩` for
the `↔`, and `obtain` + angle brackets in each direction.
"

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H K : Subgroup G) : H ⊓ K = K ⊓ H := by
  Hint "Start with `ext x` to reduce to element-wise membership."
  ext x
  Hint "Split the `↔` with `refine ⟨?_, ?_⟩`."
  refine ⟨?_, ?_⟩
  · Hint "**Forward**: `intro hx`, unpack with `rw [Subgroup.mem_inf] at hx`,
    destructure, and rebuild in swapped order."
    intro hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hH, hK⟩ := hx
    Hint (hidden := true) "`rw [Subgroup.mem_inf]; exact ⟨hK, hH⟩`"
    rw [Subgroup.mem_inf]
    exact ⟨hK, hH⟩
  · Hint "**Backward**: same pattern, opposite direction."
    intro hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hK, hH⟩ := hx
    Hint (hidden := true) "`rw [Subgroup.mem_inf]; exact ⟨hH, hK⟩`"
    rw [Subgroup.mem_inf]
    exact ⟨hH, hK⟩

Conclusion
"
The two directions are mirror images — `obtain` the components,
swap, rebuild. This is `ext` + `obtain` working together fluently.

Now you're ready for the boss: building an intersection subgroup from
scratch.
"
