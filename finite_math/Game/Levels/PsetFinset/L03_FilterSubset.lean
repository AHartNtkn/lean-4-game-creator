import Game.Metadata

World "PsetFinset"
Level 3

Title "Filter Preserves Containment"

Introduction "
# Filter + Intersection Integration

If you start with a smaller set ($s \\cap t$ instead of $s$), then
filtering gives a smaller result:

$$(s \\cap t).\\text{filter}\\; p \\;\\subseteq\\; s.\\text{filter}\\; p$$

The proof is element-chasing: unfold filter and intersection,
extract the parts, reassemble what you need.
"

/-- Filtering an intersection gives a subset of filtering the first set. -/
Statement (s t : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (s ∩ t).filter p ⊆ s.filter p := by
  Hint "A subset proof means: for every element on the left, show
  it belongs to the right. How do you unfold a subset goal?"
  rw [Finset.subset_iff]
  intro x hx
  Hint (hidden := true) "Unfold `hx` with `rw [Finset.mem_filter] at hx`,
  then `obtain ⟨hst, hp⟩ := hx`.
  Unfold `hst` with `rw [Finset.mem_inter] at hst`.
  Build the goal: `rw [Finset.mem_filter]; exact ⟨hst.1, hp⟩`."
  rw [Finset.mem_filter] at hx
  obtain ⟨hst, hp⟩ := hx
  rw [Finset.mem_inter] at hst
  rw [Finset.mem_filter]
  constructor
  · exact hst.1
  · exact hp

Conclusion "
The pattern: unfold everything, extract the parts, reassemble.

The `x ∈ t` component was extracted but not needed — it came along
for the ride from the intersection but isn't required for the right-hand
filter. Keeping exactly the parts you need is the essence of subset proofs.
"

/-- `Finset.filter_subset_filter` states monotonicity of filter:
if `s ⊆ t` then `s.filter p ⊆ t.filter p`. -/
TheoremDoc Finset.filter_subset_filter as "Finset.filter_subset_filter" in "Finset"

/-- `Finset.filter_inter_distrib` states that filter distributes
over intersection: `(s ∩ t).filter p = s.filter p ∩ t.filter p`. -/
TheoremDoc Finset.filter_inter_distrib as "Finset.filter_inter_distrib" in "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.inter_subset_left Finset.inter_subset_right inf_le_left inf_le_right Finset.mem_of_mem_filter Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.mem_inter_of_mem Finset.filter_subset_filter Finset.filter_inter_distrib
