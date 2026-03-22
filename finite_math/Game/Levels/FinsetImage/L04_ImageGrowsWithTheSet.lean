import Game.Metadata

World "FinsetImage"
Level 4

Title "Image Grows with the Set"

Introduction "
# Larger Input, Larger Image

If $y \\in f(S)$, then certainly $y \\in f(S \\cup T)$ — adding more
inputs to $f$ can only give more outputs.

This level combines **both directions** of `Finset.mem_image`:
- **Backward**: extract the witness from the hypothesis `y ∈ s.image f`
- **Forward**: re-use the witness to prove `y ∈ (s ∪ t).image f`

**Your task**: Given `h : y ∈ s.image f`, prove `y ∈ (s ∪ t).image f`.

Strategy: extract the witness `x` from `h` (with `x ∈ s` and
`f x = y`), then provide the SAME witness for the larger set,
noting that `x ∈ s` implies `x ∈ s ∪ t`.
"

/-- If y is in the image of s, it's in the image of any superset. -/
Statement (f : ℕ → ℕ) (s t : Finset ℕ) (y : ℕ) (h : y ∈ s.image f) :
    y ∈ (s ∪ t).image f := by
  Hint "First, extract the witness from `h`. Use
  `rw [Finset.mem_image] at h` to unwrap the existential."
  rw [Finset.mem_image] at h
  Hint "Now use `obtain ⟨x, hx, hfx⟩ := h` to get the witness `x`,
  its membership `hx : x ∈ s`, and `hfx : f x = y`."
  obtain ⟨x, hx, hfx⟩ := h
  Hint "Now build the membership proof for the larger set.
  Use `rw [Finset.mem_image]` on the goal to convert it to
  an existential."
  rw [Finset.mem_image]
  Hint "Provide the SAME witness: `use x`."
  use x
  Hint "Split with `constructor`. For the membership part,
  `x ∈ s` implies `x ∈ s ∪ t` — use `rw [Finset.mem_union]`
  and `left`."
  constructor
  · Hint "Use `rw [Finset.mem_union]` to convert `x ∈ s ∪ t`
    into `x ∈ s ∨ x ∈ t`. Then `left` and `exact hx`."
    rw [Finset.mem_union]
    left
    exact hx
  · Hint (hidden := true) "The functional equation hasn't changed.
    Use `exact hfx`."
    exact hfx

Conclusion "
This level showed the **extract-and-reuse** pattern:
1. Extract: `rw [mem_image] at h; obtain ⟨x, hx, hfx⟩ := h`
2. Reuse: `rw [mem_image]; use x; constructor`

The witness `x` and its functional equation `f x = y` transfer
unchanged — only the membership proof needs to be strengthened
from `x ∈ s` to `x ∈ s ∪ t`.

In plain math: if $x \\in S$ witnesses $y \\in f(S)$, then the same
$x$ witnesses $y \\in f(S \\cup T)$, since $S \\subseteq S \\cup T$.

This pattern arises whenever you need to show that image is
**monotone**: bigger input sets produce bigger images.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_union Finset.image_subset_iff Finset.subset_union_left Finset.subset_union_right Finset.mem_union_left Finset.mem_union_right le_sup_left le_sup_right
