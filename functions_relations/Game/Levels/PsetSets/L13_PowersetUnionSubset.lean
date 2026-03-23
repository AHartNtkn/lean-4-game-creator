import Game.Metadata

World "PsetSets"
Level 13

Title "Powerset Union Subset"

TheoremTab "Set"

Introduction "
# Problem Set: Level 13

In Level 12, you disproved `𝒫 (s ∪ t) = 𝒫 s ∪ 𝒫 t` — the powerset
does NOT distribute over union as an equality. But one direction DOES
hold:

$$\\mathcal{P}\\, s \\cup \\mathcal{P}\\, t \\subseteq \\mathcal{P}\\,(s \\cup t)$$

In words: if a set is a subset of `s` or a subset of `t`, then it is
a subset of `s ∪ t`. The converse fails because a subset of `s ∪ t`
can draw elements from BOTH `s` and `t`, without being contained in
either one alone — which is exactly what your counterexample showed.

**Proof strategy**: Case-split on which powerset `u` came from,
convert powerset membership to subset relations, then show that each
case gives a subset of the union.
"

/-- The powerset union is contained in the powerset of the union. -/
Statement (α : Type) (s t : Set α) :
    𝒫 s ∪ 𝒫 t ⊆ 𝒫 (s ∪ t) := by
  Hint "Start with `intro u hu` for the subset proof, then
  case-split on which powerset `u` came from."
  intro u hu
  Hint "Case-split on `hu : u ∈ 𝒫 s ∨ u ∈ 𝒫 t` with `cases hu`."
  Hint (hidden := true) "Key move: `cases hu with | inl hps | inr hpt`
  then convert to subset relations with `rw [Set.mem_powerset_iff]`."
  cases hu with
  | inl hps =>
    Hint "`hps : u ∈ 𝒫 s`. Convert both hypothesis and goal to subset
    relations with `rw [Set.mem_powerset_iff] at hps ⊢`."
    rw [Set.mem_powerset_iff] at hps ⊢
    Hint "You have `hps : u ⊆ s` and goal `u ⊆ s ∪ t`. For any
    `x ∈ u`, use `hps` to get `x ∈ s`, then `left`."
    Hint (hidden := true) "`intro x hx` then `left` then `exact hps hx`."
    intro x hx
    left
    exact hps hx
  | inr hpt =>
    Hint "`hpt : u ∈ 𝒫 t`. Same approach but use `right`."
    rw [Set.mem_powerset_iff] at hpt ⊢
    Hint (hidden := true) "`intro x hx` then `right` then `exact hpt hx`."
    intro x hx
    right
    exact hpt hx

Conclusion "
You proved `𝒫 s ∪ 𝒫 t ⊆ 𝒫 (s ∪ t)` — the direction that DOES hold.

**The pattern: equality fails, but one direction holds.** This is a
fundamental phenomenon in set theory:
- `𝒫 (s ∩ t) = 𝒫 s ∩ 𝒫 t` — full equality (Level 11)
- `𝒫 (s ∪ t) ≠ 𝒫 s ∪ 𝒫 t` — equality fails (Level 12)
- `𝒫 s ∪ 𝒫 t ⊆ 𝒫 (s ∪ t)` — but one direction holds (this level)

This pattern recurs throughout mathematics, especially when studying
**images of functions**: `f '' (s ∩ t) ⊆ f '' s ∩ f '' t` but equality
can fail. Knowing which direction holds (and why the other fails) is a
key skill you will use in the Image and Preimage worlds.
"

/-- `Set.powerset_mono` states `s ⊆ t → 𝒫 s ⊆ 𝒫 t`. -/
TheoremDoc Set.powerset_mono as "Set.powerset_mono" in "Set"

/-- `Set.subset_union_left` states `s ⊆ s ∪ t`. -/
TheoremDoc Set.subset_union_left as "Set.subset_union_left" in "Set"

/-- `Set.subset_union_right` states `t ⊆ s ∪ t`. -/
TheoremDoc Set.subset_union_right as "Set.subset_union_right" in "Set"

/-- `le_sup_left` states `a ≤ a ⊔ b`. -/
TheoremDoc le_sup_left as "le_sup_left" in "Set"
/-- `le_sup_right` states `b ≤ a ⊔ b`. -/
TheoremDoc le_sup_right as "le_sup_right" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.powerset_mono Set.subset_union_left Set.subset_union_right le_sup_left le_sup_right
