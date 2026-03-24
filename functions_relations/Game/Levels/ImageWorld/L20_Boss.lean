import Game.Metadata

World "ImageWorld"
Level 20

Title "Boss: Closing the Image-Preimage Gap"

TheoremTab "Set"

Introduction "
# Boss: f '' (f ⁻¹' t) = t When t ⊆ range f

In Level 14, you proved `f '' (f ⁻¹' t) ⊆ t` -- the ⊆ direction
always holds. Now you will prove the full EQUALITY, under the
condition that every element of `t` is in the range of `f`:

$$t \\subseteq \\text{range}(f) \\;\\;\\Longrightarrow\\;\\; f(f^{-1}(t)) = t$$

The hypothesis `h : t ⊆ Set.range f` says: for every `y ∈ t`,
there exists some `x` with `f x = y`. This is exactly the
surjectivity condition needed to close the gap.

The proof combines several skills from this world:
- `ext` for set equality (Subset World)
- `constructor` for biconditional (baseline)
- Image membership destructuring with `rintro ⟨x, hx, rfl⟩` (L03)
- Image membership construction with `exact ⟨x, ..., rfl⟩` (L06)
- Range membership destructuring (L11)
- Preimage membership unfolding (Preimage World)

**Proof plan**:
1. `ext y` then `constructor`
2. **⊆ direction**: Destructure image membership, use preimage
   hypothesis directly (same as Level 14)
3. **⊇ direction**: From `y ∈ t`, use surjectivity `h hy` to get
   `x` with `f x = y`, then build image membership
"

/-- The image-preimage roundtrip is the identity when the target
is contained in the range. -/
Statement (α β : Type) (f : α → β) (t : Set β) (h : t ⊆ Set.range f) :
    f '' (f ⁻¹' t) = t := by
  Hint "Start with `ext y` then `constructor`."
  ext y
  constructor
  -- ⊆ direction: y ∈ f '' (f ⁻¹' t) → y ∈ t
  · Hint "**⊆ direction**: This is Level 13 again. Destructure the
    image membership and the preimage hypothesis gives you the answer."
    Hint (hidden := true) "`rintro ⟨x, hx, rfl⟩` then `exact hx`."
    Branch
      intro hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hx
    rintro ⟨x, hx, rfl⟩
    Hint "`hx : x ∈ f ⁻¹' t` is definitionally `f x ∈ t`. The goal
    is `f x ∈ t`."
    exact hx
  -- ⊇ direction: y ∈ t → y ∈ f '' (f ⁻¹' t)
  · Hint "**⊇ direction**: This is the new part. You have `y ∈ t` and
    need `y ∈ f '' (f ⁻¹' t)`.

    The hypothesis `h : t ⊆ Set.range f` gives you a preimage: since
    `y ∈ t`, we have `h hy : y ∈ Set.range f`, meaning `∃ x, f x = y`.

    Use `intro hy` to get `hy : y ∈ t`."
    intro hy
    Hint "Apply the surjectivity hypothesis: `h hy` gives
    `y ∈ Set.range f`, which means `∃ x, f x = y`.

    Use `obtain ⟨x, rfl⟩ := h hy` to get the witness `x` and
    substitute `y = f x`."
    Hint (hidden := true) "`obtain ⟨x, rfl⟩ := h hy` then
    `exact ⟨x, hy, rfl⟩`."
    obtain ⟨x, rfl⟩ := h hy
    Hint "After substitution, `hy : f x ∈ t` (was `y ∈ t`, now
    `y = f x`). The goal is `f x ∈ f '' (f ⁻¹' t)`.

    Build the image membership: the witness is `x`, and `x ∈ f ⁻¹' t`
    is `f x ∈ t` which is `hy`."
    Hint (hidden := true) "`exact ⟨x, hy, rfl⟩`"
    Branch
      use x
      exact ⟨hy, rfl⟩
    exact ⟨x, hy, rfl⟩

Conclusion "
Congratulations -- you completed **Image World**!

The boss proof combined every skill from this world:

**⊆ direction** (Level 14 revisited):
```
rintro ⟨x, hx, rfl⟩
exact hx
```

**⊇ direction** (new -- uses surjectivity):
```
intro hy
obtain ⟨x, rfl⟩ := h hy
exact ⟨x, hy, rfl⟩
```

The key insight in the ⊇ direction: the hypothesis `h : t ⊆ Set.range f`
gives you a PREIMAGE for every element of `t`. Once you have a preimage
`x` with `f x = y`, building the image membership is straightforward.
This is the witness transfer pattern from L06, applied in a new context:
the witness comes from the surjectivity hypothesis instead of a subset
hypothesis.

## The Complete Image Library

| Level | Statement | Library name |
|---|---|---|
| L04 | `f '' ∅ = ∅` | `Set.image_empty` |
| L05 | `f '' (singleton a) = (singleton (f a))` | (image of singleton) |
| L06 | `s ⊆ t → f '' s ⊆ f '' t` | `Set.image_mono` |
| L07 | `f '' (s ∪ t) = f '' s ∪ f '' t` | `Set.image_union` |
| L08 | `f '' (s ∩ t) ⊆ f '' s ∩ f '' t` | `Set.image_inter_subset` |
| L10 | `(g ∘ f) '' s = g '' (f '' s)` | `Set.image_comp` |
| L12 | `f '' Set.univ = Set.range f` | `Set.image_univ` |
| L13 | `f '' s ⊆ t ↔ s ⊆ f ⁻¹' t` | `Set.image_subset_iff` |
| L14 | `f '' (f ⁻¹' t) ⊆ t` | `Set.image_preimage_subset` |
| L15 | `s ⊆ f ⁻¹' (f '' s)` | `Set.subset_preimage_image` |
| L16 | Monotonicity from Galois connection | (re-derives `Set.image_mono`) |
| L17 | Image-preimage gap from Galois | (re-derives `Set.image_preimage_subset`) |
| L18 | `Set.Nonempty s → Set.Nonempty (f '' s)` | `Set.Nonempty.image` |
| L19 | `Set.Nonempty (f '' s) → Set.Nonempty s` | (converse) |

## The Central Asymmetry

| Property | Preimage | Image |
|---|---|---|
| Preserves `∪` | ✓ (equality) | ✓ (equality) |
| Preserves `∩` | ✓ (equality) | Only ⊆ |
| Preserves `ᶜ` | ✓ (equality) | No |
| Roundtrip with inverse | `f ⁻¹' (f '' s) ⊇ s` | `f '' (f ⁻¹' t) ⊆ t` |
| Roundtrip = identity | Requires injectivity | Requires surjectivity |

The structural reason: preimage involves only universal quantification
and logical connectives, which commute with everything. Image involves
an existential, which only commutes with disjunction -- not with
conjunction or negation.

**Monotonicity from the Galois connection (L16)**: In Level 16, you
re-derived image monotonicity (L06) from the Galois connection (L13)
and the preimage-image embedding (L15). In Level 17, you re-derived
the image-preimage gap (L14) from the same Galois connection. This demonstrated that
adjunctions automatically imply monotonicity -- a deep structural
principle.

**Looking ahead**: In the problem set (PsetImgPreimg), you will
practice these results on fresh problems. Then in Injective World
and Surjective World, you will explore when the gaps close and when
the ⊆ for intersection becomes an equality.
"

-- TheoremDocs for theorems disabled here but documented in other levels
-- (L18 only imports Game.Metadata, so it cannot see docs from L12/L13)

/-- `Set.image_preimage_subset` states `f '' (f ⁻¹' t) ⊆ t`. Applying
the function to the preimage gives back a subset of the original. -/
TheoremDoc Set.image_preimage_subset as "Set.image_preimage_subset" in "Set"

/-- `Set.subset_preimage_image` states `s ⊆ f ⁻¹' (f '' s)`. Every
element of `s` is in the preimage of the image -- the preimage-image
roundtrip never loses elements, but it may gain extras. -/
TheoremDoc Set.subset_preimage_image as "Set.subset_preimage_image" in "Set"

-- P0 fix: disable all library lemmas that one-shot the boss
/-- `Set.image_preimage_eq_of_subset` states that if `s ⊆ Set.range f`,
then `f '' (f ⁻¹' s) = s`. This is exactly the boss statement --
disabled to force manual proof. -/
TheoremDoc Set.image_preimage_eq_of_subset as "Set.image_preimage_eq_of_subset" in "Set"

/-- `Set.image_preimage_eq_iff` characterizes when `f '' (f ⁻¹' s) = s`
holds. Disabled to prevent boss bypass. -/
TheoremDoc Set.image_preimage_eq_iff as "Set.image_preimage_eq_iff" in "Set"

/-- `Set.image_preimage_eq_inter_range` states
`f '' (f ⁻¹' s) = s ∩ Set.range f`. Disabled to prevent boss bypass. -/
TheoremDoc Set.image_preimage_eq_inter_range as "Set.image_preimage_eq_inter_range" in "Set"

/-- `Set.image_preimage_eq_range_inter` states
`f '' (f ⁻¹' s) = Set.range f ∩ s`. Disabled to prevent boss bypass. -/
TheoremDoc Set.image_preimage_eq_range_inter as "Set.image_preimage_eq_range_inter" in "Set"

/-- `Set.image_preimage_eq` states that for surjective `f`,
`f '' (f ⁻¹' s) = s`. Disabled to prevent boss bypass. -/
TheoremDoc Set.image_preimage_eq as "Set.image_preimage_eq" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_preimage_subset Set.subset_preimage_image Iff.rfl Set.image_preimage_eq_of_subset Set.image_preimage_eq_iff Set.image_preimage_eq_inter_range Set.image_preimage_eq_range_inter Set.image_preimage_eq
