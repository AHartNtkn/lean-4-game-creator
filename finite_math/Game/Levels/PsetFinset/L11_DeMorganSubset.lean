import Game.Metadata

World "PsetFinset"
Level 11

Title "De Morgan Subset"

Introduction "
# Set Identity: De Morgan Direction

Prove that removing elements in `t` and removing elements in `u`
separately, then taking the union, gives a subset of removing
elements in `t ∩ u`:

$$(s \\setminus t) \\cup (s \\setminus u) \\;\\subseteq\\; s \\setminus (t \\cap u)$$

In words: if $x$ is in $s$ but missing from $t$ (or missing from $u$),
then $x$ is certainly in $s$ but missing from $t \\cap u$ (since it's
not in both $t$ and $u$).

This combines `mem_union`, `mem_sdiff`, `mem_inter`, `cases`, and
negation handling — skills from all three lecture worlds.
"

/-- De Morgan direction: removing separately, then unioning, gives a subset. -/
Statement (s t u : Finset ℕ) : (s \ t) ∪ (s \ u) ⊆ s \ (t ∩ u) := by
  rw [Finset.subset_iff]
  intro x hx
  Hint "Unfold the union membership in `hx` and case-split."
  rw [Finset.mem_union] at hx
  rw [Finset.mem_sdiff, Finset.mem_inter]
  Hint (hidden := true) "`cases hx with` then unfold sdiff in each case.
  In `inl`: `h.1` gives `x ∈ s`, and `h.2 : x ∉ t` gives
  `intro ⟨ht, _⟩; exact h.2 ht`.
  In `inr`: same pattern with `u`."
  cases hx with
  | inl h =>
    rw [Finset.mem_sdiff] at h
    constructor
    · exact h.1
    · intro ⟨ht, _⟩
      exact h.2 ht
  | inr h =>
    rw [Finset.mem_sdiff] at h
    constructor
    · exact h.1
    · intro ⟨_, hu⟩
      exact h.2 hu

Conclusion "
This is the set-theoretic De Morgan law applied as a subset:
$$(s \\setminus t) \\cup (s \\setminus u) \\subseteq s \\setminus (t \\cap u)$$

The key move: in each case, you have `x ∉ t` (or `x ∉ u`), and
the goal requires `x ∉ t ∩ u`. Since `t ∩ u ⊆ t` (and `⊆ u`),
non-membership of the smaller set follows from non-membership of
the individual component.

The reverse inclusion also holds (giving equality), but requires
excluded middle (`by_cases` on `x ∈ t`), which is disabled in this pset.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.inter_subset_left Finset.inter_subset_right inf_le_left inf_le_right Finset.subset_union_left Finset.subset_union_right le_sup_left le_sup_right sdiff_sup Finset.sdiff_inter_distrib_left Finset.sdiff_inter_distrib_right
