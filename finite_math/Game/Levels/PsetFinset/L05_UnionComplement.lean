import Game.Metadata

World "PsetFinset"
Level 5

Title "Union Complement"

Introduction "
# Subtracting a Component from a Union

Prove that $(s \\cup t) \\setminus t \\subseteq s$.

If $x$ is in $s \\cup t$ but not in $t$, then $x$ must have come
from $s$.

The proof combines `mem_sdiff`, `mem_union`, and `cases`.
"

/-- Removing one component from a union leaves a subset of the other. -/
Statement (s t : Finset ℕ) : (s ∪ t) \ t ⊆ s := by
  rw [Finset.subset_iff]
  intro x hx
  Hint "Unfold `hx` with `rw [Finset.mem_sdiff] at hx` then
  `obtain` the parts."
  rw [Finset.mem_sdiff] at hx
  obtain ⟨hut, hnt⟩ := hx
  rw [Finset.mem_union] at hut
  Hint "You have `hut : x ∈ s ∨ x ∈ t` and `hnt : x ∉ t`.
  Case-split on the disjunction — one branch gives the goal directly,
  the other contradicts `hnt`."
  Hint (hidden := true) "Use `cases hut with`. In `inl`, you have
  `hxs : x ∈ s` — that's the goal. In `inr`, you have `hxt : x ∈ t`
  contradicting `hnt` — use `exact absurd hxt hnt`."
  cases hut with
  | inl hxs => exact hxs
  | inr hxt => exact absurd hxt hnt

Conclusion "
A direct case split resolved this cleanly:
- **inl** ($x \\in s$): this IS the goal — `exact hxs`
- **inr** ($x \\in t$): contradicts `hnt : x \\notin t` —
  `absurd hxt hnt` closes the goal

No `by_contra` needed. When a disjunction has one branch that
gives the goal directly and another that contradicts a hypothesis,
a direct case split is the simplest approach.
"

/-- `sdiff_le_self` states `a \ b ≤ a` in a lattice. -/
TheoremDoc sdiff_le_self as "sdiff_le_self" in "Order"

/-- `Finset.sdiff_subset` states `s \ t ⊆ s`. -/
TheoremDoc Finset.sdiff_subset as "Finset.sdiff_subset" in "Finset"

/-- `sdiff_le` states `a \ b ≤ a` (alternate name for sdiff_le_self). -/
TheoremDoc sdiff_le as "sdiff_le" in "Order"

/-- `sdiff_le_iff` states `a \ b ≤ c ↔ a ≤ b ⊔ c` in a Heyting algebra. -/
TheoremDoc sdiff_le_iff as "sdiff_le_iff" in "Order"

/-- `sdiff_le_iff'` is the commuted form: `a \ b ≤ c ↔ a ≤ c ⊔ b`. -/
TheoremDoc sdiff_le_iff' as "sdiff_le_iff'" in "Order"

/-- `sdiff_le_iff_left` states `a \ b ≤ b ↔ a ≤ b`. -/
TheoremDoc sdiff_le_iff_left as "sdiff_le_iff_left" in "Order"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.inter_subset_left Finset.inter_subset_right Finset.subset_union_left Finset.subset_union_right inf_le_left inf_le_right le_sup_left le_sup_right Finset.mem_union_left Finset.mem_union_right sdiff_le_self Finset.sdiff_subset sdiff_le sdiff_le_iff sdiff_le_iff' sdiff_le_iff_left Finset.union_sdiff_right Finset.union_sdiff_left sup_sdiff_right_self sup_sdiff_left_self
