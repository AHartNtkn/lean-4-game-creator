import Game.Metadata

World "PsetFinset"
Level 4

Title "Union and Intersection Subset"

Introduction "
# Union Retrieval

Prove that $(s \\cap t) \\cup u \\subseteq s \\cup u$.

The intersection $s \\cap t$ is contained in $s$, so anything in
$(s \\cap t) \\cup u$ is either in $s$ (via the intersection) or
in $u$ — both land in $s \\cup u$.

This combines `subset_iff`, `mem_union`, `mem_inter`, and `cases`.
"

/-- Intersecting before taking a union can only shrink the first component. -/
Statement (s t u : Finset ℕ) : s ∩ t ∪ u ⊆ s ∪ u := by
  Hint "A subset proof means: for every element on the left, show
  it belongs to the right. How do you unfold a subset goal?"
  rw [Finset.subset_iff]
  intro x hx
  Hint (hidden := true) "Unfold `hx` with `rw [Finset.mem_union] at hx`,
  then `rw [Finset.mem_union]` on the goal and case-split with
  `cases hx with`. In the `inl` case, unfold the intersection to
  extract `x ∈ s`. In the `inr` case, `x ∈ u` maps directly."
  rw [Finset.mem_union] at hx
  rw [Finset.mem_union]
  cases hx with
  | inl h =>
    rw [Finset.mem_inter] at h
    left
    exact h.1
  | inr h =>
    right
    exact h

Conclusion "
The case split on union membership is the key move. Each branch
routes to the correct side of the target union:
- From $s \\cap t$: extract $x \\in s$, then `left`
- From $u$: directly `right`
"

/-- `sup_le_sup_right` states monotonicity of ⊔ on the right:
if `a ≤ b` then `a ⊔ c ≤ b ⊔ c`. -/
TheoremDoc sup_le_sup_right as "sup_le_sup_right" in "Order"

/-- `sup_le_sup_left` states monotonicity of ⊔ on the left:
if `a ≤ b` then `c ⊔ a ≤ c ⊔ b`. -/
TheoremDoc sup_le_sup_left as "sup_le_sup_left" in "Order"

/-- `Finset.union_subset_iff` states `s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u`. -/
TheoremDoc Finset.union_subset_iff as "Finset.union_subset_iff" in "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.inter_subset_left Finset.inter_subset_right Finset.subset_union_left Finset.subset_union_right inf_le_left inf_le_right le_sup_left le_sup_right Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right sup_le_sup_right sup_le_sup_left Finset.union_subset_iff Finset.union_subset_union_left Finset.union_subset_union_right Finset.union_subset_union
