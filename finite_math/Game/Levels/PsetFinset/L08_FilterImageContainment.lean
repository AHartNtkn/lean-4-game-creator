import Game.Metadata

World "PsetFinset"
Level 8

Title "Filter Image Containment"

Introduction "
# Filter + Image Integration

Prove that filtering a set and then taking its image gives a
subset of the image of the original set:

$$(s.\\text{filter}\\; p).\\text{image}\\; f \\;\\subseteq\\; s.\\text{image}\\; f$$

The proof combines backward image extraction, filter unwrapping,
and forward image construction.
"

/-- Filtering before imaging gives a subset of imaging directly. -/
Statement (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℕ) :
    (s.filter p).image f ⊆ s.image f := by
  rw [Finset.subset_iff]
  intro y hy
  Hint "Extract the witness from `hy` using backward image membership."
  Hint (hidden := true) "`rw [Finset.mem_image] at hy` then
  `obtain ⟨x, hx, hfx⟩ := hy`. Unfold the filter:
  `rw [Finset.mem_filter] at hx`. Build the goal:
  `rw [Finset.mem_image]; exact ⟨x, hx.1, hfx⟩`."
  rw [Finset.mem_image] at hy
  obtain ⟨x, hx, hfx⟩ := hy
  rw [Finset.mem_filter] at hx
  rw [Finset.mem_image]
  exact ⟨x, hx.1, hfx⟩

Conclusion "
The key insight: the witness `x` works for both sides. From the
filtered image, `x ∈ s.filter p` means `x ∈ s ∧ p x`. The filter
predicate `p x` is discarded — only `x ∈ s` is needed for the
unfiltered image.

This mirrors L03 (filter preserves containment) but with image
instead of intersection: filtering can only shrink, so the image
of the filtered set is contained in the image of the whole set.
"

/-- `Finset.filter_subset p s` states that `s.filter p ⊆ s`:
filtering can only remove elements, never add them. -/
TheoremDoc Finset.filter_subset as "Finset.filter_subset" in "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_subset_iff Finset.filter_subset Finset.mem_of_mem_filter
