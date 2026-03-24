import Game.Metadata

World "ImageWorld"
Level 6

Title "Image Preserves Subsets"

TheoremTab "Set"

Introduction "
# Image Is Monotone

If `s ⊆ t`, then `f '' s ⊆ f '' t`. In words: a bigger input set
produces a bigger output set. This is **monotonicity** of image.

Why? If `y ∈ f '' s`, there exists `x ∈ s` with `f x = y`. Since
`s ⊆ t`, we have `x ∈ t`. So the SAME witness `x` proves `y ∈ f '' t`.

This is your first abstract image proof. It is also your first
chance to use `rintro` on a subset proof. The subset goal
`f '' s ⊆ f '' t` means `∀ y, y ∈ f '' s → y ∈ f '' t`, so
`rintro y ⟨x, hx, rfl⟩` destructures the image membership.

**Proof plan**:
1. `rintro y ⟨x, hx, rfl⟩` -- introduce `y` and destructure
2. Construct the new image membership using the SAME witness `x`
"

/-- If s ⊆ t then f '' s ⊆ f '' t. -/
Statement (α β : Type) (f : α → β) (s t : Set α) (h : s ⊆ t) :
    f '' s ⊆ f '' t := by
  Hint "The goal is `f '' s ⊆ f '' t`. This means: for every `y` in the
  image of `s`, show `y` is in the image of `t`.

  Use `rintro y ⟨x, hx, rfl⟩` to introduce `y` and destructure the
  image membership hypothesis."
  Hint (hidden := true) "`rintro y ⟨x, hx, rfl⟩` then
  `exact ⟨x, h hx, rfl⟩`."
  Branch
    intro y hy
    Hint "Destructure `hy` with `obtain ⟨x, hx, rfl⟩ := hy`."
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, h hx, rfl⟩
  rintro y ⟨x, hx, rfl⟩
  Hint "You have `x : α` and `hx : x ∈ s`. The goal is `f x ∈ f '' t`,
  meaning `∃ z ∈ t, f z = f x`.

  The witness is `x` itself. Since `h : s ⊆ t`, we have `h hx : x ∈ t`.
  Use `exact ⟨x, h hx, rfl⟩` to provide the witness, membership, and
  equation in one step."
  Hint (hidden := true) "Alternatively, step by step: `use x`,
  `constructor`, `exact h hx`, `rfl`."
  Branch
    use x
    constructor
    · exact h hx
    · rfl
  exact ⟨x, h hx, rfl⟩

Conclusion "
You proved image monotonicity: `s ⊆ t → f '' s ⊆ f '' t`.

The proof was just two steps:
1. `rintro y ⟨x, hx, rfl⟩` -- destructure image membership
2. `exact ⟨x, h hx, rfl⟩` -- reconstruct with updated membership

**The image proof idiom**: This two-step pattern -- destructure then
reconstruct -- is the core idiom for image proofs:

```
rintro y ⟨x, hx, rfl⟩   -- get the witness
exact ⟨x, ..., rfl⟩      -- repackage it
```

You modify what goes in the `...` (here: upgrading `hx` via `h`),
but the structure stays the same. You will see this pattern in every
image proof in this world.

**Anonymous constructors for images**: `exact ⟨x, hx, rfl⟩` constructs
`∃ z, z ∈ t ∧ f z = f x` by providing:
- `x` as the witness
- `hx` for membership
- `rfl` for the equation `f x = f x`

This is the compact way to build image membership. You can also use
`use x; constructor; exact hx; rfl` for the same effect.

**The witness transfer pattern**: Notice how the proof works: you
destructure to get a witness `x ∈ s`, then RE-USE the same witness
to build membership in `f '' t`. The witness transfers between sets
-- only its membership proof changes (from `hx : x ∈ s` to
`h hx : x ∈ t`). This pattern recurs throughout Image World: the
same element serves as witness in both the deconstruction and
reconstruction. Watch for it in Levels 6, 7, and beyond.

**Does the converse hold?** If `f '' s ⊆ f '' t`, must `s ⊆ t`? No!
Consider the constant function `f(n) = 0`. Then `f '' s = f '' t = {0}`
for any nonempty `s` and `t`, so `f '' s ⊆ f '' t` is trivially true
regardless of whether `s ⊆ t`. Injectivity is needed for the converse
-- you will explore this in Injective World.

**Why `Set.mem_image_of_mem` is disabled**: In library code, you would
write `exact Set.mem_image_of_mem f (h hx)` to construct image membership
in one step. We disable it so you learn the witness construction
`exact ⟨x, h hx, rfl⟩` -- understanding HOW image membership is built
is essential for the proofs ahead.

**Comparison with preimage monotonicity** (Preimage World Level 5):
preimage monotonicity was `exact h hx` -- one step! Image monotonicity
needs `exact ⟨x, h hx, rfl⟩` -- the existential witness adds overhead.
This is the tax of the existential.

The library name is `Set.image_mono`.
"

/-- `Set.image_mono` states that if `s ⊆ t` then `f '' s ⊆ f '' t`.
Image is monotone: bigger input set implies bigger output set. -/
TheoremDoc Set.image_mono as "Set.image_mono" in "Set"

NewTheorem Set.image_mono

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_mono
