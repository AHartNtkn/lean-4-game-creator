import Game.Metadata

World "PsetFinset"
Level 6

Title "Image of a Nonempty Set"

Introduction "
# Nonempty + Image Retrieval

If a finset $s$ is nonempty, then its image under any function $f$
is also nonempty.

The proof combines:
- `obtain` to extract a witness from the nonempty hypothesis
- Forward image membership to place the witness in the image
"

/-- The image of a nonempty finset is nonempty. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) (h : s.Nonempty) :
    ∃ y, y ∈ s.image f := by
  Hint "The nonempty hypothesis guarantees at least one element
  exists. Can you extract a concrete witness from it?"
  obtain ⟨x, hx⟩ := h
  Hint (hidden := true) "Provide the witness `f x` with `use f x`.
  Then prove `f x ∈ s.image f` using the forward membership pattern:
  `rw [Finset.mem_image]; exact ⟨x, hx, rfl⟩`."
  use f x
  rw [Finset.mem_image]
  exact ⟨x, hx, rfl⟩

Conclusion "
Two skills combined:
- **Nonempty extraction**: `obtain ⟨x, hx⟩ := h` pulls out a
  concrete element and its membership proof
- **Forward image membership**: the witness for `f x` in the image
  is `x` itself, with `f x = f x` by `rfl`
"

/-- `Finset.Nonempty.image` states that the image of a nonempty finset
is nonempty: `s.Nonempty → (s.image f).Nonempty`. -/
TheoremDoc Finset.Nonempty.image as "Finset.Nonempty.image" in "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.Nonempty.image
