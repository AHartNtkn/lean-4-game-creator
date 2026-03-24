import Game.Metadata

World "ImageWorld"
Level 12

Title "Image of Everything is the Range"

TheoremTab "Set"

Introduction "
# Connecting Image and Range

In Level 11, you learned that `Set.range f` is the set of all outputs
of `f`. There is a direct connection to image: the range IS the image
of the universal set `Set.univ` (the set of ALL inputs):

$$\\text{range}(f) = f(\\text{univ})$$

In Lean: `f '' Set.univ = Set.range f`.

This makes intuitive sense: the range is what you get when you apply
`f` to everything -- and `Set.univ` IS everything.

**Your task**: Prove this equality.

**Proof plan**:
1. `ext y` then `constructor`
2. **Forward**: `rintro ⟨x, _, rfl⟩` -- destructure image membership.
   The source membership `x ∈ Set.univ` is trivially true, so discard
   it with `_`. Build range membership with `exact ⟨x, rfl⟩`.
3. **Backward**: `rintro ⟨x, rfl⟩` -- destructure range membership.
   Build image membership with the universal membership
   `Set.mem_univ x`.

**New fact**: `Set.mem_univ x` proves `x ∈ Set.univ` -- everything
is in the universal set.
"

/-- The image of the universal set is the range. -/
Statement (α β : Type) (f : α → β) :
    f '' Set.univ = Set.range f := by
  Hint "Start with `ext y` then `constructor`."
  ext y
  constructor
  -- Forward: y ∈ f '' Set.univ → y ∈ Set.range f
  · Hint "**Forward**: `y ∈ f '' Set.univ` means `∃ x ∈ Set.univ, f x = y`.
    Since every `x` is in `Set.univ`, the source membership is trivial.

    Use `rintro ⟨x, _, rfl⟩` -- the `_` discards the trivial
    `x ∈ Set.univ` proof."
    Hint (hidden := true) "`rintro ⟨x, _, rfl⟩` then `exact ⟨x, rfl⟩`."
    Branch
      intro hy
      obtain ⟨x, _, rfl⟩ := hy
      exact ⟨x, rfl⟩
    rintro ⟨x, _, rfl⟩
    Hint "The goal is `f x ∈ Set.range f`, which means `∃ z, f z = f x`.
    The witness is `x` itself."
    Hint (hidden := true) "`exact ⟨x, rfl⟩`"
    exact ⟨x, rfl⟩
  -- Backward: y ∈ Set.range f → y ∈ f '' Set.univ
  · Hint "**Backward**: `y ∈ Set.range f` means `∃ x, f x = y`.
    Use `rintro ⟨x, rfl⟩` to destructure -- note the simpler pattern
    (two components, not three) since range has no source set."
    Hint (hidden := true) "`rintro ⟨x, rfl⟩` then
    `exact ⟨x, Set.mem_univ x, rfl⟩`."
    Branch
      intro hy
      obtain ⟨x, rfl⟩ := hy
      exact ⟨x, Set.mem_univ x, rfl⟩
    rintro ⟨x, rfl⟩
    Hint "The goal is `f x ∈ f '' Set.univ`. Build the image membership:
    the witness is `x`, the source membership is `Set.mem_univ x`
    (everything is in `Set.univ`), and `f x = f x` by `rfl`."
    Hint (hidden := true) "`exact ⟨x, Set.mem_univ x, rfl⟩`"
    exact ⟨x, Set.mem_univ x, rfl⟩

Conclusion "
You proved `f '' Set.univ = Set.range f` -- the range is the image
of everything!

**Image vs Range destructuring**: Notice the pattern difference:
- Image: `rintro ⟨x, hx, rfl⟩` -- three components (witness,
  membership, equation)
- Range: `rintro ⟨x, rfl⟩` -- two components (witness, equation)

Range drops the source membership because `∃ x, f x = y` has no
set constraint, while `∃ x ∈ s, f x = y` does.

**`Set.mem_univ`**: The proof `Set.mem_univ x : x ∈ Set.univ` says
everything is in the universal set. This is the bridge from range
back to image -- range membership `⟨x, rfl⟩` becomes image membership
`⟨x, Set.mem_univ x, rfl⟩` by adding the trivial membership proof.

The library name is `Set.image_univ`.
"

/-- `Set.image_univ` states `f '' Set.univ = Set.range f`.
The image of the universal set is the range of the function.

## When to use it
When you need to convert between image-of-everything and range.
-/
TheoremDoc Set.image_univ as "Set.image_univ" in "Set"

NewTheorem Set.image_univ

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_univ
