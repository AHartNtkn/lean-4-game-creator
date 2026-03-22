import Game.Metadata

World "FinsetImage"
Level 5

Title "Image Distributes Over Union"

Introduction "
# Image and Union: One Direction

Level 4 showed that if $y \\in f(S)$, then $y \\in f(S \\cup T)$ — a
larger input can only give more outputs. This level proves the
**reverse redistribution**: if $y \\in f(S \\cup T)$, then $y$ must
come from $f(S)$ or $f(T)$ (or both).

Together with Level 4, this establishes that image distributes
over union: $f(S \\cup T) = f(S) \\cup f(T)$.

**Your task**: Given `h : x ∈ (s ∪ t).image f`, prove
`x ∈ s.image f ∪ t.image f`.

Strategy:
1. Extract the witness `a` from `h` (backward extraction)
2. Determine whether `a ∈ s` or `a ∈ t` (case split on union)
3. Provide the same witness for the appropriate side
"

/-- If x is in the image of a union, it's in the union of the images. -/
Statement (f : ℕ → ℕ) (s t : Finset ℕ) (x : ℕ)
    (h : x ∈ (s ∪ t).image f) :
    x ∈ s.image f ∪ t.image f := by
  Hint "Extract the witness from `h`. Use `rw [Finset.mem_image] at h`
  to unwrap the existential."
  rw [Finset.mem_image] at h
  Hint "Use `obtain ⟨a, ha, hfa⟩ := h` to get the witness `a`,
  its membership `ha : a ∈ s ∪ t`, and `hfa : f a = x`."
  obtain ⟨a, ha, hfa⟩ := h
  Hint "Now `ha : a ∈ s ∪ t`. Use `rw [Finset.mem_union] at ha`
  to split into `a ∈ s ∨ a ∈ t`."
  rw [Finset.mem_union] at ha
  Hint "The goal is `x ∈ s.image f ∪ t.image f`.
  Use `rw [Finset.mem_union]` to convert it to a disjunction,
  then case-split on `ha` with `cases ha with | inl hl => ... | inr hr => ...`."
  rw [Finset.mem_union]
  Hint (hidden := true) "Try `cases ha with` then handle each case
  using `left` or `right` and the forward membership pattern."
  cases ha with
  | inl hl =>
    Hint "In this case, `hl : a ∈ s`. Use `left` to target `s.image f`,
    then provide the witness."
    left
    rw [Finset.mem_image]
    exact ⟨a, hl, hfa⟩
  | inr hr =>
    Hint "In this case, `hr : a ∈ t`. Use `right` to target `t.image f`,
    then provide the witness."
    right
    rw [Finset.mem_image]
    exact ⟨a, hr, hfa⟩

Conclusion "
You've proved one direction: every element of $f(S \\cup T)$
belongs to $f(S) \\cup f(T)$. Combined with Level 4 (the other
direction), this establishes $f(S \\cup T) = f(S) \\cup f(T)$.

The next level proves this full equality using `ext`.

The proof pattern: extract the witness from the combined image,
determine which input set it came from (case split), then
redirect it to the corresponding output set. The witness and
its functional equation transfer unchanged — only the membership
routing changes.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_union Finset.image_subset_iff Finset.subset_union_left Finset.subset_union_right Finset.mem_union_left Finset.mem_union_right le_sup_left le_sup_right
