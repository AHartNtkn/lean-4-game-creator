import Game.Metadata

World "PsetSets"
Level 11

Title "Powerset of Intersection"

TheoremTab "Set"

Introduction "
# Problem Set: Level 11

Prove the full equality `𝒫 (s ∩ t) = 𝒫 s ∩ 𝒫 t`.

In words: the subsets of `s ∩ t` are exactly the sets that are subsets
of `s` AND subsets of `t`.

This combines powerset membership from Indexed Operations World with
intersection from Set Operations World. You will need to convert between
powerset membership and subset relations.
"

/-- `Set.powerset_mono` states `s ⊆ t → 𝒫 s ⊆ 𝒫 t`. -/
TheoremDoc Set.powerset_mono as "Set.powerset_mono" in "Set"

/-- The powerset of an intersection equals the intersection of the
powersets. -/
Statement (α : Type) (s t : Set α) : 𝒫 (s ∩ t) = 𝒫 s ∩ 𝒫 t := by
  Hint "Start with `ext u` then `constructor` for the set equality."
  ext u
  constructor
  -- Forward: u ∈ 𝒫 (s ∩ t) → u ∈ 𝒫 s ∩ 𝒫 t
  · Hint "Convert `u ∈ 𝒫 (s ∩ t)` to a subset relation with
    `rw [Set.mem_powerset_iff]`, then split the conjunction."
    intro hu
    rw [Set.mem_powerset_iff] at hu
    Hint "Now `hu : u ⊆ s ∩ t`. Use `constructor` to split the goal
    into `u ∈ 𝒫 s` and `u ∈ 𝒫 t`."
    constructor
    · Hint "Show `u ∈ 𝒫 s`. Convert with `rw [Set.mem_powerset_iff]`,
      then prove `u ⊆ s` by extracting the first component."
      Hint (hidden := true) "Key move: `rw [Set.mem_powerset_iff]` converts
      powerset membership to a subset relation."
      rw [Set.mem_powerset_iff]
      intro x hx
      exact (hu hx).1
    · Hint "Show `u ∈ 𝒫 t`. Same approach, extracting the second component."
      Hint (hidden := true) "Same pattern — convert to subset, then extract `.2`."
      rw [Set.mem_powerset_iff]
      intro x hx
      exact (hu hx).2
  -- Backward: u ∈ 𝒫 s ∩ 𝒫 t → u ∈ 𝒫 (s ∩ t)
  · Hint "**Backward**: Given `u ∈ 𝒫 s ∩ 𝒫 t`, prove `u ∈ 𝒫 (s ∩ t)`.
    Destructure the conjunction, convert both to subset relations, then
    combine them."
    intro hu
    Hint "Use `obtain` to split the conjunction, then convert each
    powerset membership to a subset relation."
    Hint (hidden := true) "Key move: `obtain ⟨hus, hut⟩ := hu` then
    `rw [Set.mem_powerset_iff] at hus hut ⊢`."
    obtain ⟨hus, hut⟩ := hu
    rw [Set.mem_powerset_iff] at hus hut ⊢
    Hint "You have `hus : u ⊆ s` and `hut : u ⊆ t`. The goal is
    `u ⊆ s ∩ t`. For any `x ∈ u`, you need `x ∈ s ∧ x ∈ t` — which
    you get from `hus` and `hut`."
    intro x hx
    exact ⟨hus hx, hut hx⟩

Conclusion "
You proved the full equality `𝒫 (s ∩ t) = 𝒫 s ∩ 𝒫 t`. The proof used:
- `ext u` to reduce to element-wise membership
- `rw [Set.mem_powerset_iff]` to convert between `∈ 𝒫` and `⊆`
- Subset hypotheses as functions (`hu hx` gives `x ∈ s ∩ t`)
- Dot projections (`.1`, `.2`) to extract components from `∩`

The backward direction combined two subset hypotheses into one: if
`u ⊆ s` and `u ⊆ t`, then for any `x ∈ u`, both `hus hx` and `hut hx`
give the two components of `x ∈ s ∩ t`.

**Multi-target `rw`**: The backward direction used
`rw [Set.mem_powerset_iff] at hus hut ⊢` — rewriting at two hypotheses
AND the goal in a single command. The syntax `at h1 h2 ⊢` tells `rw`
to apply the rewrite at `h1`, then `h2`, then the goal (`⊢`). This
saves three separate `rw` calls. You can use this syntax with any `rw`
whenever you need to apply the same rewrite at multiple locations.

**Contrast with powerset of union**: `𝒫 (s ∪ t) = 𝒫 s ∪ 𝒫 t` is FALSE
in general! A subset of `s ∪ t` need not be a subset of `s` alone or
of `t` alone. (Example: `s ∪ t` itself is a subset of `s ∪ t` but is
generally not a subset of either `s` or `t`.)
"

/-- `Set.powerset_inter` states `𝒫 (s ∩ t) = 𝒫 s ∩ 𝒫 t`. -/
TheoremDoc Set.powerset_inter as "Set.powerset_inter" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.powerset_mono Set.powerset_inter
