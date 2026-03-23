import Game.Metadata

World "PsetSets"
Level 9

Title "Indexed Intersection"

TheoremTab "Set"

Introduction "
# Problem Set: Level 9

Prove that an indexed intersection with a binary intersection distributes:

$$(\\bigcap_i s_i) \\cap t \\subseteq \\bigcap_i (s_i \\cap t)$$

If `x` is in every `s i` AND in `t`, then for each `i`, `x` is in
`s i ∩ t`.

This combines indexed intersection (`Set.mem_iInter`) from Indexed
Operations World with binary intersection from Set Operations World.
"

/-- Indexed intersection distributes into binary intersection (⊆). -/
Statement (α : Type) (ι : Type) (s : ι → Set α) (t : Set α) :
    (⋂ i, s i) ∩ t ⊆ ⋂ i, (s i ∩ t) := by
  Hint "Start with `intro x hx` then destructure the binary intersection."
  intro x hx
  obtain ⟨hinter, ht⟩ := hx
  Hint "You have `hinter : x ∈ ⋂ i, s i` and `ht : x ∈ t`. The goal
  is `x ∈ ⋂ i, (s i ∩ t)`. Use `rw [Set.mem_iInter]` then `intro i`."
  Hint (hidden := true) "Key move: `rw [Set.mem_iInter]` converts the
  indexed intersection goal to a universal statement."
  rw [Set.mem_iInter]
  intro i
  Hint "Build `x ∈ s i ∩ t` with `constructor`. Extract `x ∈ s i`
  from the indexed intersection hypothesis."
  constructor
  · rw [Set.mem_iInter] at hinter
    exact hinter i
  · exact ht

Conclusion "
The proof pattern for distributing `⋂` into `∩`:
1. Destructure the binary intersection
2. Convert the `⋂` goal to a universal (`rw [Set.mem_iInter]`)
3. Introduce the index
4. Build the binary intersection using the extracted `∀` and the
   binary component

This is the indexed analogue of the binary distributivity from Level 3.
The `rw [Set.mem_iInter]` step bridges between set notation and
quantifier logic.

**Note**: The reverse inclusion `⋂ i, (s i ∩ t) ⊆ (⋂ i, s i) ∩ t`
also holds, giving the full equality. The reverse direction is even
simpler — try it on paper.
"

/-- `Set.subset_iInter` states `(∀ i, s ⊆ t i) → s ⊆ ⋂ i, t i`. -/
TheoremDoc Set.subset_iInter as "Set.subset_iInter" in "Set"

/-- `Set.iInter_subset` states `⋂ i, s i ⊆ s j` for any index `j`. -/
TheoremDoc Set.iInter_subset as "Set.iInter_subset" in "Set"

/-- `Set.inter_subset_inter_left` states `s ⊆ t → s ∩ u ⊆ t ∩ u`. -/
TheoremDoc Set.inter_subset_inter_left as "Set.inter_subset_inter_left" in "Set"

/-- `Set.inter_subset_inter_right` states `s ⊆ t → u ∩ s ⊆ u ∩ t`. -/
TheoremDoc Set.inter_subset_inter_right as "Set.inter_subset_inter_right" in "Set"

/-- `le_iInf` states `(∀ i, a ≤ f i) → a ≤ ⨅ i, f i` (lattice version of subset_iInter). -/
TheoremDoc le_iInf as "le_iInf" in "Set"

/-- `iInf_le` states `⨅ i, f i ≤ f j` (lattice version of iInter_subset). -/
TheoremDoc iInf_le as "iInf_le" in "Set"

/-- `Set.inter_iInter` states `s ∩ ⋂ i, t i = ⋂ i, s ∩ t i`. -/
TheoremDoc Set.inter_iInter as "Set.inter_iInter" in "Set"

/-- `Set.iInter_inter` states `(⋂ i, s i) ∩ t = ⋂ i, s i ∩ t`. -/
TheoremDoc Set.iInter_inter as "Set.iInter_inter" in "Set"

/-- `inf_iInf_eq` is the lattice version: `a ⊓ ⨅ i, f i = ⨅ i, a ⊓ f i`. -/
TheoremDoc inf_iInf_eq as "inf_iInf_eq" in "Set"

/-- `iInf_inf_eq` is the lattice version: `(⨅ i, f i) ⊓ a = ⨅ i, f i ⊓ a`. -/
TheoremDoc iInf_inf_eq as "iInf_inf_eq" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.subset_iInter Set.iInter_subset Set.inter_subset_inter_left Set.inter_subset_inter_right le_iInf iInf_le Set.inter_iInter Set.iInter_inter inf_iInf_eq iInf_inf_eq
