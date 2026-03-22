import Game.Metadata

World "PsetFinset"
Level 12

Title "Image Monotonicity"

Introduction "
# Subsets Map to Subsets

If $s \\subseteq t$, then $f(s) \\subseteq f(t)$ — imaging preserves
the subset relation.

The proof combines backward image extraction (to get a witness from
`y ∈ s.image f`), the subset hypothesis (to promote the witness from
`s` to `t`), and forward image construction (to place the witness in
`t.image f`).
"

/-- Image preserves subsets: s ⊆ t implies s.image f ⊆ t.image f. -/
Statement (f : ℕ → ℕ) (s t : Finset ℕ) (h : s ⊆ t) : s.image f ⊆ t.image f := by
  rw [Finset.subset_iff]
  intro y hy
  Hint "Extract the witness from `hy`: some `x ∈ s` with `f x = y`.
  Then use the subset hypothesis to promote `x ∈ s` to `x ∈ t`."
  Hint (hidden := true) "`rw [Finset.mem_image] at hy`
  `obtain ⟨x, hxs, hfx⟩ := hy`
  `rw [Finset.subset_iff] at h`
  `rw [Finset.mem_image]`
  `exact ⟨x, h hxs, hfx⟩`"
  rw [Finset.mem_image] at hy
  obtain ⟨x, hxs, hfx⟩ := hy
  rw [Finset.subset_iff] at h
  rw [Finset.mem_image]
  exact ⟨x, h hxs, hfx⟩

Conclusion "
The pattern: extract the witness, promote it through the subset, then
rebuild the image membership. The function `f` is the same in both
directions — only the container changes from `s` to `t`.

This is `Finset.image_subset_image` (or `Finset.image_mono`) in
Mathlib. The proof shows why it works: the witness `x` in the
smaller set is also in the larger set, so `f x` is in both images.
"

/-- `Finset.image_subset_image` states monotonicity of image:
if `s ⊆ t` then `s.image f ⊆ t.image f`. -/
TheoremDoc Finset.image_subset_image as "Finset.image_subset_image" in "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_subset_iff
