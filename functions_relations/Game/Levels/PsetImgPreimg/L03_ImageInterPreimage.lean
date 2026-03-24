import Game.Metadata

World "PsetImgPreimg"
Level 3

Title "Image Meets Preimage"

TheoremTab "Set"

Introduction "
# Image of (s ∩ f ⁻¹' t) = f '' s ∩ t

Here is a beautiful identity that combines image and preimage:

$$f(s \\cap f^{-1}(t)) = f(s) \\cap t$$

In words: if you restrict `s` to only those elements whose outputs
land in `t`, and then push forward, you get exactly the outputs that
come from `s` AND lie in `t`.

Unlike `f '' (s \\cap u) \\subseteq f '' s \\cap f '' u` (which was only
a subset), here we get **equality**. Why? Because one side of the
intersection is a PREIMAGE, which commutes perfectly with the
existential in image membership.

**Proof plan**: `ext y` then `constructor`. Each direction destructures
one side and reassembles for the other.
"

/-- The image of s intersected with a preimage equals the image
intersected with the target. -/
Statement (α β : Type) (f : α → β) (s : Set α) (t : Set β) :
    f '' (s ∩ f ⁻¹' t) = f '' s ∩ t := by
  ext y
  constructor
  -- Forward: y ∈ f '' (s ∩ f ⁻¹' t) → y ∈ f '' s ∩ t
  · Hint "Destructure the image membership. The source set is
    `s \\cap f ⁻¹' t`, so the witness satisfies BOTH `x \\in s` and
    `f x \\in t`. Use `rintro ⟨x, ⟨hxs, hxt⟩, rfl⟩`."
    Hint (hidden := true) "`rintro ⟨x, ⟨hxs, hxt⟩, rfl⟩` then
    `exact ⟨⟨x, hxs, rfl⟩, hxt⟩`."
    Branch
      intro hy
      obtain ⟨x, ⟨hxs, hxt⟩, rfl⟩ := hy
      exact ⟨⟨x, hxs, rfl⟩, hxt⟩
    rintro ⟨x, ⟨hxs, hxt⟩, rfl⟩
    exact ⟨⟨x, hxs, rfl⟩, hxt⟩
  -- Backward: y ∈ f '' s ∩ t → y ∈ f '' (s ∩ f ⁻¹' t)
  · Hint "Destructure `f '' s \\cap t` to get `x \\in s` with `f x = y`
    and `y \\in t`. Use `rintro ⟨⟨x, hxs, rfl⟩, hft⟩`."
    Hint (hidden := true) "`rintro ⟨⟨x, hxs, rfl⟩, hft⟩` then
    `exact ⟨x, ⟨hxs, hft⟩, rfl⟩`."
    Branch
      intro hy
      obtain ⟨⟨x, hxs, rfl⟩, hft⟩ := hy
      exact ⟨x, ⟨hxs, hft⟩, rfl⟩
    rintro ⟨⟨x, hxs, rfl⟩, hft⟩
    exact ⟨x, ⟨hxs, hft⟩, rfl⟩

Conclusion "
You proved `f '' (s \\cap f ⁻¹' t) = f '' s \\cap t`.

Both directions used the same witness `x` — you just rearranged
the components. The forward direction split the intersection
membership into source and preimage parts; the backward direction
reassembled them.

**Why equality holds here but not for f '' (s \\cap u)**: In Image
World, `f '' (s \\cap t) \\subseteq f '' s \\cap f '' t` was only a
subset because the intersection of images uses DIFFERENT witnesses.
Here, one side is `t` (a set of outputs), not `f '' t` (an image).
The preimage `f ⁻¹' t` translates `t` into input-space, where it
intersects cleanly with `s`. No phantom intersections are possible.

**Connecting to the image-preimage adjunction**: This identity is
closely related to `f '' s \\subseteq t \\Leftrightarrow s \\subseteq f ⁻¹' t`
(proved in Image World). Both express how image and preimage
interconvert cleanly when one side stays in its natural domain.
Concretely, this identity says: restricting inputs to those that
land in `t`, then pushing forward, gives exactly the outputs from
`s` that are in `t`.

The library name is `Set.image_inter_preimage`.
"

/-- `Set.image_inter_preimage` states
`f '' (s \\cap f ⁻¹' t) = f '' s \\cap t`.
Image distributes over intersection with a preimage. -/
TheoremDoc Set.image_inter_preimage as "Set.image_inter_preimage" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_inter_preimage Iff.rfl
