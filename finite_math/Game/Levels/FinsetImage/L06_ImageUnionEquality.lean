import Game.Metadata

World "FinsetImage"
Level 6

Title "Image Distributes Over Union: Full Equality"

Introduction "
# Proving the Full Equality

Levels 4 and 5 established both directions of the image-union
relationship:
- **Level 4**: $y \\in f(S) \\implies y \\in f(S \\cup T)$ (image grows)
- **Level 5**: $y \\in f(S \\cup T) \\implies y \\in f(S) \\cup f(T)$
  (elements route to one side)

Together they give the fundamental identity:

$$f(S \\cup T) = f(S) \\cup f(T)$$

To prove a **finset equality**, use `ext`:
```
ext x  -- reduces A = B to: x \\in A \\leftrightarrow x \\in B
```

This reduces the equality to a membership biconditional. Then use
`constructor` to split into the two directions and apply the
patterns from Levels 4 and 5.

**Your task**: Prove the full equality using `ext` and both
membership directions.
"

/-- Image distributes over union as a full equality. -/
Statement (f : ℕ → ℕ) (s t : Finset ℕ) :
    (s ∪ t).image f = s.image f ∪ t.image f := by
  Hint "Use `ext y` to reduce the finset equality to a membership
  equivalence: `y ∈ (s ∪ t).image f ↔ y ∈ s.image f ∪ t.image f`."
  ext y
  Hint "The goal is an iff. Use `constructor` to split into both
  directions."
  constructor
  -- Forward: y ∈ (s ∪ t).image f → y ∈ s.image f ∪ t.image f
  · Hint "This is Level 5's argument: extract the witness, determine
    which set it came from, and route to the correct side.
    Start with `intro h` then `rw [Finset.mem_image] at h`."
    intro h
    rw [Finset.mem_image] at h
    Hint "Use `obtain ⟨a, ha, hfa⟩ := h` to extract the witness."
    obtain ⟨a, ha, hfa⟩ := h
    Hint "Now `ha : a ∈ s ∪ t`. Use `rw [Finset.mem_union] at ha`
    to split into cases, then `rw [Finset.mem_union]` on the goal."
    rw [Finset.mem_union] at ha
    rw [Finset.mem_union]
    Hint (hidden := true) "Try `cases ha with` then use `left`/`right`
    with `rw [Finset.mem_image]; exact ⟨a, ..., hfa⟩`."
    cases ha with
    | inl hl =>
      left
      rw [Finset.mem_image]
      exact ⟨a, hl, hfa⟩
    | inr hr =>
      right
      rw [Finset.mem_image]
      exact ⟨a, hr, hfa⟩
  -- Backward: y ∈ s.image f ∪ t.image f → y ∈ (s ∪ t).image f
  · Hint "This is the reverse: extract the witness from whichever
    side of the union it came from, then embed it into `s ∪ t`.
    Start with `intro h` then `rw [Finset.mem_union] at h`."
    intro h
    rw [Finset.mem_union] at h
    Hint (hidden := true) "Try `cases h with` then extract the
    witness and embed into the union."
    cases h with
    | inl hl =>
      Hint "Extract the witness from `hl : y ∈ s.image f`, then
      provide it for `y ∈ (s ∪ t).image f` with `a ∈ s ∪ t`
      via `rw [Finset.mem_union]` and `left`."
      rw [Finset.mem_image] at hl
      obtain ⟨a, ha, hfa⟩ := hl
      rw [Finset.mem_image]
      use a
      constructor
      · rw [Finset.mem_union]; left; exact ha
      · exact hfa
    | inr hr =>
      Hint "Same pattern for the right side."
      rw [Finset.mem_image] at hr
      obtain ⟨a, ha, hfa⟩ := hr
      rw [Finset.mem_image]
      use a
      constructor
      · rw [Finset.mem_union]; right; exact ha
      · exact hfa

Conclusion "
You proved the **full identity**: $f(S \\cup T) = f(S) \\cup f(T)$.

The proof used `ext` to reduce equality to mutual membership,
then applied the forward direction (Level 5's argument) and the
backward direction (Level 4's pattern for both sides).

This identity says **image is a homomorphism** from the
finset union algebra to itself: it preserves the union operation.

Compare with intersection, where this breaks down — you'll see
why in Level 8.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_union Finset.image_subset_iff Finset.subset_union_left Finset.subset_union_right Finset.mem_union_left Finset.mem_union_right le_sup_left le_sup_right
