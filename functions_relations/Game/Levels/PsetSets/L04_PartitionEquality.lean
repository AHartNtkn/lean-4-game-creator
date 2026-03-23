import Game.Metadata

World "PsetSets"
Level 4

Title "Partition Identity"

TheoremTab "Set"

Introduction "
# Problem Set: Level 4

Prove the **partition identity**: every set equals the union of its
part inside `t` and its part outside `t`:

$$s = (s \\cap t) \\cup (s \\setminus t)$$

Think about what tools you have for proving set equality, and why
one approach might be more natural than the other here. For the
forward direction, consider what information you need to choose a side
of the union.
"

/-- A set equals the union of its intersection and difference with t. -/
Statement (α : Type) (s t : Set α) : s = (s ∩ t) ∪ (s \ t) := by
  Hint "Use `apply Set.Subset.antisymm` to prove equality from two
  subset inclusions."
  apply Set.Subset.antisymm
  -- Forward: s ⊆ (s ∩ t) ∪ (s \ t)
  · Hint "**Forward**: Given `x ∈ s`, show `x ∈ (s ∩ t) ∪ (s \\ t)`.
    You need to decide whether `x ∈ t` to choose the correct side.
    Use `by_cases ht : x ∈ t`."
    intro x hx
    Hint (hidden := true) "Key move: `by_cases ht : x ∈ t` splits into
    two cases — then `left` or `right` with the appropriate pair."
    by_cases ht : x ∈ t
    · Hint "`ht : x ∈ t`. Combined with `hx : x ∈ s`, you can build
      `x ∈ s ∩ t`. Use `left`."
      left
      exact ⟨hx, ht⟩
    · Hint "`ht : x ∉ t`. Combined with `hx : x ∈ s`, you can build
      `x ∈ s \\ t`. Use `right`."
      right
      exact ⟨hx, ht⟩
  -- Backward: (s ∩ t) ∪ (s \ t) ⊆ s
  · Hint "**Backward**: In both cases (`x ∈ s ∩ t` or `x ∈ s \\ t`),
    `x ∈ s` is the first component."
    intro x hx
    Hint (hidden := true) "Key move: `cases hx` and extract `.1` in both."
    cases hx with
    | inl h =>
      Hint (hidden := true) "`h : x ∈ s ∩ t` — the first component `.1` gives `x ∈ s`."
      exact h.1
    | inr h =>
      Hint (hidden := true) "`h : x ∈ s \\ t` — the first component `.1` gives `x ∈ s`."
      exact h.1

Conclusion "
You proved the partition identity `s = (s ∩ t) ∪ (s \\ t)`. This says
every set splits into two disjoint pieces relative to any other set:
the elements in `t` and the elements not in `t`.

**Key techniques**:
- `Set.Subset.antisymm` to split equality into two subset proofs —
  an alternative to `ext` when the structure is clearer as two inclusions
- `by_cases ht : x ∈ t` for classical case analysis — necessary when
  you need to choose a side of a disjunction but do not know which

Compare this to `ext` + `constructor`: both prove set equality, but
`antisymm` lets you think in terms of subsets (\"everything in `s` is
in the union\" and \"everything in the union is in `s`\"), which is
sometimes more natural.
"

/-- `Set.inter_union_diff` states `s ∩ t ∪ s \\ t = s`. -/
TheoremDoc Set.inter_union_diff as "Set.inter_union_diff" in "Set"

/-- `sup_inf_sdiff` is the lattice version: `x ⊓ y ⊔ x \\ y = x`. -/
TheoremDoc sup_inf_sdiff as "sup_inf_sdiff" in "Set"

/-- `Set.diff_union_inter` states `s \\ t ∪ s ∩ t = s`. -/
TheoremDoc Set.diff_union_inter as "Set.diff_union_inter" in "Set"

/-- `sup_sdiff_inf` is the lattice version: `x \\ y ⊔ x ⊓ y = x`. -/
TheoremDoc sup_sdiff_inf as "sup_sdiff_inf" in "Set"

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
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.inter_union_diff sup_inf_sdiff Set.diff_union_inter sup_sdiff_inf le_antisymm sup_le inf_le_left le_sup_left le_sup_right inf_le_right
