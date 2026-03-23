import Game.Metadata

World "PsetSets"
Level 3

Title "Distributivity (⊆)"

TheoremTab "Set"

Introduction "
# Problem Set: Level 3

Prove a **distributivity** inclusion for abstract sets. In Set Operations
World, you proved `s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u)`. Here is a
different arrangement — and only the `⊆` direction:

$$(s \\cup t) \\cap u \\subseteq (s \\cap u) \\cup (t \\cap u)$$

**Proof strategy**: `intro x hx`, destructure the intersection,
case-split on the union, then build the appropriate side.
"

/-- Right distributivity of ∩ over ∪ (subset direction). -/
Statement (α : Type) (s t u : Set α) :
    (s ∪ t) ∩ u ⊆ (s ∩ u) ∪ (t ∩ u) := by
  Hint "Start with `intro x hx` for the subset proof. Then destructure
  the intersection and case-split on the union."
  intro x hx
  Hint (hidden := true) "Key move: `obtain` splits the intersection
  hypothesis, then `cases` splits the union."
  obtain ⟨hsu, hu⟩ := hx
  Hint "Now `hsu : x ∈ s ∪ t` and `hu : x ∈ u`. Case-split on the union."
  cases hsu with
  | inl hs =>
    Hint "`hs : x ∈ s` and `hu : x ∈ u`. Build the left side of the union."
    Hint (hidden := true) "`left` then `exact ⟨hs, hu⟩`."
    left
    exact ⟨hs, hu⟩
  | inr ht =>
    Hint "`ht : x ∈ t` and `hu : x ∈ u`. Build the right side."
    Hint (hidden := true) "`right` then `exact ⟨ht, hu⟩`."
    right
    exact ⟨ht, hu⟩

Conclusion "
The proof followed the standard pattern for distributivity:
1. Destructure the intersection (`obtain`)
2. Case-split on the union (`cases ... with | inl | inr`)
3. Build the correct side (`left`/`right` + anonymous constructor)

Compare to the Set Operations World boss: same logical structure,
different arrangement of `s`, `t`, `u`.
"

/-- `Set.inter_union_distrib_left` states `s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u`. -/
TheoremDoc Set.inter_union_distrib_left as "Set.inter_union_distrib_left" in "Set"

/-- `inf_sup_left` is the lattice version: `a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c`. -/
TheoremDoc inf_sup_left as "inf_sup_left" in "Set"

/-- `Set.union_inter_distrib_right` is the dual distributivity law. -/
TheoremDoc Set.union_inter_distrib_right as "Set.union_inter_distrib_right" in "Set"

/-- `sup_inf_right` is the lattice version of the dual distributivity. -/
TheoremDoc sup_inf_right as "sup_inf_right" in "Set"

/-- `Set.inter_distrib_left` is an alias for `Set.inter_union_distrib_left`. -/
TheoremDoc Set.inter_distrib_left as "Set.inter_distrib_left" in "Set"

/-- `and_or_left` states `a ∧ (b ∨ c) ↔ a ∧ b ∨ a ∧ c`. -/
TheoremDoc and_or_left as "and_or_left" in "Set"

/-- `and_or_right` states `(a ∨ b) ∧ c ↔ a ∧ c ∨ b ∧ c`. -/
TheoremDoc and_or_right as "and_or_right" in "Set"

/-- `or_and_left` states `a ∨ b ∧ c ↔ (a ∨ b) ∧ (a ∨ c)`. -/
TheoremDoc or_and_left as "or_and_left" in "Set"

/-- `or_and_right` states `a ∧ b ∨ c ↔ (a ∨ c) ∧ (b ∨ c)`. -/
TheoremDoc or_and_right as "or_and_right" in "Set"

/-- `inf_sup_right` is the lattice version: `(a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c`. -/
TheoremDoc inf_sup_right as "inf_sup_right" in "Set"

/-- `sup_inf_left` is the lattice dual: `a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)`. -/
TheoremDoc sup_inf_left as "sup_inf_left" in "Set"

/-- `le_antisymm` states `a ≤ b → b ≤ a → a = b` (lattice antisymmetry). -/
TheoremDoc le_antisymm as "le_antisymm" in "Set"
/-- `sup_le` states `a ≤ c → b ≤ c → a ⊔ b ≤ c`. -/
TheoremDoc sup_le as "sup_le" in "Set"
/-- `inf_le_left` states `a ⊓ b ≤ a`. -/
TheoremDoc inf_le_left as "inf_le_left" in "Set"
/-- `le_sup_left` states `a ≤ a ⊔ b`. -/
TheoremDoc le_sup_left as "le_sup_left" in "Set"
/-- `le_sup_right` states `b ≤ a ⊔ b`. -/
TheoremDoc le_sup_right as "le_sup_right" in "Set"
/-- `inf_le_right` states `a ⊓ b ≤ b`. -/
TheoremDoc inf_le_right as "inf_le_right" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.inter_union_distrib_left inf_sup_left Set.union_inter_distrib_right sup_inf_right Set.inter_distrib_left and_or_left and_or_right or_and_left or_and_right inf_sup_right sup_inf_left le_antisymm sup_le inf_le_left le_sup_left le_sup_right inf_le_right
