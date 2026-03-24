import Game.Metadata

World "ImageWorld"
Level 16

Title "Monotonicity from the Galois Connection"

TheoremTab "Set"

Introduction "
# Re-Deriving Monotonicity

In Level 6, you proved image monotonicity directly:
`s ⊆ t → f '' s ⊆ f '' t`. The proof was two steps: destructure,
then reconstruct with an updated membership proof.

Now you will prove the SAME result using a completely different method:
the **Galois connection** (Level 13) combined with the
**preimage-image embedding** (Level 15).

The idea:
1. By the Galois connection (`Set.image_subset_iff`), showing
   `f '' s ⊆ f '' t` is equivalent to showing `s ⊆ f ⁻¹' (f '' t)`.
2. By the preimage-image embedding (`Set.subset_preimage_image`),
   we know `t ⊆ f ⁻¹' (f '' t)`.
3. Since `s ⊆ t` and `t ⊆ f ⁻¹' (f '' t)`, transitivity gives
   `s ⊆ f ⁻¹' (f '' t)`.

This is a general principle: **Galois connections (adjunctions)
automatically imply monotonicity**. You do not need to touch
witnesses at all -- the abstract machinery does the work.

**Important**: In this level, `rintro`, `rcases`, and `obtain` are
disabled. You cannot destructure image membership directly -- you
MUST use the Galois connection approach.

**Proof plan**:
1. `rw [Set.image_subset_iff]` -- convert to the preimage form
2. `intro x hx` -- take an element of `s`
3. `apply Set.subset_preimage_image` -- reduce to membership in `t`
4. `exact h hx` -- use the subset hypothesis
"

/-- Image monotonicity re-derived from the Galois connection. -/
Statement (α β : Type) (f : α → β) (s t : Set α) (h : s ⊆ t) :
    f '' s ⊆ f '' t := by
  Hint "Use `rw [Set.image_subset_iff]` to convert the goal from
  `f '' s ⊆ f '' t` to the equivalent `s ⊆ f ⁻¹' (f '' t)`.

  This uses the Galois connection from Level 13."
  Hint (hidden := true) "`rw [Set.image_subset_iff]` then `intro x hx`,
  `apply Set.subset_preimage_image`, `exact h hx`."
  rw [Set.image_subset_iff]
  Hint "The goal is now `s ⊆ f ⁻¹' (f '' t)`. You need to show every
  element of `s` is in the preimage of `f '' t`.

  Use `intro x hx` to take an element."
  intro x hx
  Hint "The goal is `x ∈ f ⁻¹' (f '' t)`, which is `f x ∈ f '' t`.

  From Level 15, you know `Set.subset_preimage_image f t : t ⊆ f ⁻¹' (f '' t)`.
  Use `apply Set.subset_preimage_image` to reduce the goal to `x ∈ t`."
  Hint (hidden := true) "`apply Set.subset_preimage_image` then `exact h hx`."
  Branch
    exact Set.subset_preimage_image f t (h hx)
  apply Set.subset_preimage_image
  Hint "The goal is `x ∈ t`. You have `h : s ⊆ t` and `hx : x ∈ s`."
  Hint (hidden := true) "`exact h hx`"
  exact h hx

Conclusion "
You re-derived `f '' s ⊆ f '' t` from the Galois connection, without
ever touching a witness or destructuring an image membership!

Compare the two proofs:

**Direct proof (Level 6)**:
```
rintro y ⟨x, hx, rfl⟩
exact ⟨x, h hx, rfl⟩
```
This works at the element level: find the witness, upgrade its
membership, repackage.

**Galois proof (this level)**:
```
rw [Set.image_subset_iff]
intro x hx
apply Set.subset_preimage_image
exact h hx
```
This works at the structural level: convert to preimage form,
then chain two known subset relationships.

**Why this matters**: The Galois proof generalizes. ANY pair of
operations related by a Galois connection (adjunction) automatically
inherits monotonicity. This principle appears throughout mathematics:
- Image/preimage of sets
- Direct image/inverse image of sheaves
- Left/right adjoints in category theory

The Galois connection is the engine; monotonicity is a free corollary.

**Next**: Can the Galois connection also re-derive the image-preimage
gap `f '' (f ⁻¹' t) ⊆ t` (Level 14)? In the next level, you will
find out by doing the derivation yourself.
"

/-- `Set.image_subset` states `s ⊆ t → f '' s ⊆ f '' t` (same as
`Set.image_mono` but with a different argument order). Disabled to
force the Galois connection derivation. -/
TheoremDoc Set.image_subset as "Set.image_subset" in "Set"

/-- `Set.image_mono` states that if `s ⊆ t` then `f '' s ⊆ f '' t`.
Disabled here to force the Galois connection re-derivation. -/
TheoremDoc Set.image_mono as "Set.image_mono" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr rintro rcases obtain cases
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_mono Set.image_subset
