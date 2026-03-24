import Game.Metadata

World "PsetImgPreimg"
Level 5

Title "Image of Indexed Union"

TheoremTab "Set"

Introduction "
# Image Preserves Indexed Union — As Equality!

In Level 4, you proved that image of indexed intersection is only
a subset. Now for the good news: image of indexed **union** is an
**equality**:

$$f\\left(\\bigcup_i s_i\\right) = \\bigcup_i f(s_i)$$

Why equality? The forward direction says: if `y` has a witness `x`
in some `s_i`, then `y` is in `f '' (s_i)`. The backward direction
says: if `y` is in some `f '' (s_i)`, then its witness is in `s_i`,
hence in `\\bigcup_i s_i`. Both directions use the SAME witness —
no collision problem.

**Proof plan**: `ext y`, `constructor`, then each direction converts
between `Set.mem_iUnion` and existential quantification over the
index.
"

/-- Image distributes over indexed union as equality. -/
Statement (α β ι : Type) (f : α → β) (s : ι → Set α) :
    f '' (⋃ i, s i) = ⋃ i, f '' (s i) := by
  ext y
  constructor
  -- Forward: y ∈ f '' (⋃ i, s i) → y ∈ ⋃ i, f '' (s i)
  · Hint "Destructure the image membership, then convert `\\bigcup`
    to an existential with `rw [Set.mem_iUnion]`."
    Hint (hidden := true) "`rintro ⟨x, hx, rfl⟩` then
    `rw [Set.mem_iUnion] at hx` then `obtain ⟨i, hi⟩ := hx` then
    `rw [Set.mem_iUnion]` then `exact ⟨i, x, hi, rfl⟩`."
    Branch
      intro hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Set.mem_iUnion]
      exact ⟨i, x, hi, rfl⟩
    rintro ⟨x, hx, rfl⟩
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    rw [Set.mem_iUnion]
    exact ⟨i, x, hi, rfl⟩
  -- Backward: y ∈ ⋃ i, f '' (s i) → y ∈ f '' (⋃ i, s i)
  · Hint "Convert the hypothesis from indexed union to an existential,
    extract the index and image witness, then rebuild."
    Hint (hidden := true) "`intro hy` then `rw [Set.mem_iUnion] at hy`
    then `obtain ⟨i, x, hi, rfl⟩ := hy` then `use x` then
    `constructor` then `rw [Set.mem_iUnion]` then `exact ⟨i, hi⟩`
    then `rfl`."
    Branch
      intro hy
      rw [Set.mem_iUnion] at hy
      obtain ⟨i, x, hi, rfl⟩ := hy
      use x
      refine ⟨?_, rfl⟩
      rw [Set.mem_iUnion]
      exact ⟨i, hi⟩
    intro hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨i, x, hi, rfl⟩ := hy
    use x
    constructor
    · rw [Set.mem_iUnion]
      exact ⟨i, hi⟩
    · rfl

Conclusion "
You proved `f '' (\\bigcup_i s_i) = \\bigcup_i f '' (s_i)` — image
distributes over indexed union as a full equality!

Both directions used the SAME witness `x` — unlike intersections,
there is no collision problem with unions. The forward direction
found `x \\in s_i` for some `i` and placed `f x` in `f '' (s_i)`.
The backward direction found `f x \\in f '' (s_i)`, extracted `x`,
and placed `x` in `\\bigcup_i s_i`.

**The complete picture**:

| Operation | Preimage | Image |
|---|---|---|
| Binary \\cap | = | only \\subseteq |
| Indexed \\bigcap | = | only \\subseteq |
| Binary \\cup | = | = |
| Indexed \\bigcup | = | = |

Image preserves ALL unions (binary and indexed) as equalities, but
only \\subseteq for ALL intersections. The root cause: unions involve
existence (\\exists), and the existential in image membership
(`\\exists x \\in s, f x = y`) composes cleanly with another existential.
Intersections involve universality (\\forall), which clashes with the
existential — a single witness cannot serve all sets simultaneously.

The library name is `Set.image_iUnion`.
"

/-- `Set.image_iUnion` states
`f '' (\\bigcup i, s i) = \\bigcup i, f '' (s i)`.
Image distributes over indexed union as equality. -/
TheoremDoc Set.image_iUnion as "Set.image_iUnion" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_iUnion Set.image_Union Iff.rfl
