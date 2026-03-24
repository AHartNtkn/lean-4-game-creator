import Game.Metadata

World "PsetImgPreimg"
Level 1

Title "Image Subset of Range"

TheoremTab "Set"

Introduction "
# Problem Set: Level 1

Welcome to the Image & Preimage Problem Set!

This warmup level asks you to prove a fundamental fact: the image of
any set is contained in the range of the function.

$$f(s) \\subseteq \\text{range}(f)$$

Why? Every element of `f '' s` has a witness `x \\in s` with `f x = y`.
That same `x` (without the source set constraint) witnesses
`y \\in \\text{range}(f)`. The range is a bigger net — it captures ALL
outputs, not just those from `s`.

This is a subset proof: take `y \\in f '' s`, show `y \\in Set.range f`.
"

/-- The image of any set is contained in the range. -/
Statement (α β : Type) (f : α → β) (s : Set α) :
    f '' s ⊆ Set.range f := by
  Hint "Destructure the image membership with `rintro y ⟨x, hx, rfl⟩`,
  then build range membership. The source set constraint `hx` is
  irrelevant for range membership."
  Hint (hidden := true) "`rintro y ⟨x, hx, rfl⟩` then `exact ⟨x, rfl⟩`."
  Branch
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, rfl⟩
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, rfl⟩

Conclusion "
You proved `f '' s ⊆ Set.range f` — the image of any set lives inside
the range.

The proof was just two steps:
1. `rintro y ⟨x, hx, rfl⟩` — destructure image membership
2. `exact ⟨x, rfl⟩` — reconstruct as range membership

Notice that `hx : x \\in s` was never used! The source set membership
is irrelevant — if `f x = y` for ANY `x`, then `y \\in Set.range f`.
Image membership is STRONGER than range membership because it
constrains the witness to come from `s`. Dropping that constraint
makes the proof trivial.

**Image vs Range membership**:
- `y \\in f '' s` is `\\exists x, x \\in s \\wedge f x = y` — three components
- `y \\in Set.range f` is `\\exists x, f x = y` — two components

Going from image to range means forgetting one component.

**The witness transfer pattern**: This proof illustrates a strategy
you will use throughout this problem set. Every level follows the
same two-phase structure:
1. **Destructure** one kind of membership to extract a witness
2. **Reconstruct** a different kind of membership using the same
   witness (possibly with extra work)

Recognizing this pattern — destructure, then reconstruct with the
same witness — will help you see the proof path immediately in
every level that follows.

The library name is `Set.image_subset_range`.
"

/-- `Set.image_subset_range` states `f '' s ⊆ Set.range f`.
The image of any set is contained in the range of the function. -/
TheoremDoc Set.image_subset_range as "Set.image_subset_range" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_subset_range Iff.rfl
