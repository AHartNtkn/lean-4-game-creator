import Game.Metadata

World "ImageWorld"
Level 8

Title "Image Only ⊆ for Intersection"

TheoremTab "Set"

Introduction "
# The Asymmetry: Image Does NOT Preserve Intersection

Here is the critical asymmetry between image and preimage.
Preimage preserves intersection as an EQUALITY:

$$f^{-1}(s \\cap t) = f^{-1}(s) \\cap f^{-1}(t)$$

For image, we only get a SUBSET:

$$f(s \\cap t) \\subseteq f(s) \\cap f(t)$$

The ⊆ direction is easy: if `x ∈ s ∩ t`, then `x ∈ s` AND `x ∈ t`,
so the same witness `x` places `f x` in both `f '' s` and `f '' t`.

But equality can FAIL. Consider `f(n) = 0` (constant function),
`s = {0}`, `t = {1}`:
- `f '' s ∩ f '' t = {0} ∩ {0} = {0}` (nonempty!)
- `f '' (s ∩ t) = f '' ∅ = ∅` (empty!)

The intersection of the images can be strictly larger than the image
of the intersection. The constant function \"collapses\" distinct
inputs to the same output, creating phantom intersections.

**Your task**: Prove the ⊆ direction. This is a subset proof, not
a set equality.

**Proof plan**:
1. `rintro y ⟨x, hx, rfl⟩` -- destructure image of intersection
2. Destructure `hx : x ∈ s ∩ t` into `hs : x ∈ s` and `ht : x ∈ t`
3. Build the conjunction: `f x ∈ f '' s` and `f x ∈ f '' t`
"

/-- Image of intersection is a subset of intersection of images. -/
Statement (α β : Type) (f : α → β) (s t : Set α) :
    f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  Hint "This is a subset proof. Use `rintro y ⟨x, hx, rfl⟩` to
  introduce and destructure the image membership."
  Hint (hidden := true) "After destructuring, `hx : x ∈ s ∩ t`. Use
  `obtain ⟨hs, ht⟩ := hx` to split, then build both sides with
  `constructor`."
  Branch
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨hs, ht⟩ := hx
    constructor
    · exact ⟨x, hs, rfl⟩
    · exact ⟨x, ht, rfl⟩
  rintro y ⟨x, hx, rfl⟩
  Hint "`hx : x ∈ s ∩ t` is a conjunction. Destructure it with
  `obtain ⟨hs, ht⟩ := hx` to get `hs : x ∈ s` and `ht : x ∈ t`."
  obtain ⟨hs, ht⟩ := hx
  Hint "Now build the intersection of images: you need
  `f x ∈ f '' s ∧ f x ∈ f '' t`. Use `constructor` to split."
  constructor
  · Hint "Prove `f x ∈ f '' s`. The witness is `x` with `hs : x ∈ s`."
    Hint (hidden := true) "`exact ⟨x, hs, rfl⟩`"
    exact ⟨x, hs, rfl⟩
  · Hint "Prove `f x ∈ f '' t`. The witness is `x` with `ht : x ∈ t`."
    Hint (hidden := true) "`exact ⟨x, ht, rfl⟩`"
    exact ⟨x, ht, rfl⟩

Conclusion "
You proved `f '' (s ∩ t) ⊆ f '' s ∩ f '' t`. Notice: only ⊆, not =.

**Why equality fails**: The reverse inclusion `f '' s ∩ f '' t ⊆ f '' (s ∩ t)`
would require: given witnesses `x₁ ∈ s` and `x₂ ∈ t` with
`f x₁ = f x₂ = y`, finding some `x ∈ s ∩ t` with `f x = y`.
But `x₁` and `x₂` might be DIFFERENT elements! There is no reason
that either one is in `s ∩ t`.

**The constant function counterexample**: Let `f(n) = 0`, `s = \\{0\\}`,
`t = \\{1\\}`:
- `0 ∈ f '' s` (witness: `0 ∈ s` and `f 0 = 0`)
- `0 ∈ f '' t` (witness: `1 ∈ t` and `f 1 = 0`)
- So `0 ∈ f '' s ∩ f '' t`
- But `s ∩ t = ∅`, so `f '' (s ∩ t) = ∅`

The problem is that the witnesses are DIFFERENT (`0` vs `1`). The
constant function collapses distinct inputs, creating intersections
in the image that do not correspond to intersections in the domain.

**The witness transfer pattern**: Once again, the proof re-uses the
SAME witness `x` from `s ∩ t`. Since `x ∈ s` AND `x ∈ t`, the same
witness works for both `f '' s` and `f '' t` simultaneously.

**When does equality hold?** If `f` is INJECTIVE, then the witnesses
must be the same (`f x₁ = f x₂ → x₁ = x₂`), and equality holds.
You will prove this in Injective World.

**The quantifier logic**: Why does union work but intersection fail?
Image membership is existential: `y ∈ f '' s ↔ ∃ x ∈ s, f x = y`.
For union, the existential distributes: `∃ x, (P x ∨ Q x)` is
equivalent to `(∃ x, P x) ∨ (∃ x, Q x)`. One witness suffices
either way. For intersection, the existential does NOT distribute:
`∃ x, (P x ∧ Q x)` implies `(∃ x, P x) ∧ (∃ x, Q x)`, but NOT
the reverse -- the two existential witnesses might be different
elements. This is exactly the gap you just proved.

**Updated scoreboard**:

| Operation | Preimage | Image | Why? |
|---|---|---|---|
| `∪` (union) | = | = | `∃` distributes over `∨` |
| `∩` (intersection) | = | only ⊆ | `∃` does NOT distribute over `∧` |
| `ᶜ` (complement) | = | no relation | `∃` does not commute with `¬` in either direction: `∃ x, ¬P x` neither implies nor is implied by `¬(∃ x, P x)` when `f` is not injective |

The library name is `Set.image_inter_subset`.
"

/-- `Set.image_inter_subset` states
`f '' (s ∩ t) ⊆ f '' s ∩ f '' t`. Image of intersection is contained
in intersection of images, but equality may fail. -/
TheoremDoc Set.image_inter_subset as "Set.image_inter_subset" in "Set"

NewTheorem Set.image_inter_subset

/-- `Set.image_mono` states that if `s ⊆ t` then `f '' s ⊆ f '' t`.
Image is monotone. Disabled to force manual proof. -/
TheoremDoc Set.image_mono as "Set.image_mono" in "Set"

/-- `Set.image_subset` states `s ⊆ t → f '' s ⊆ f '' t` (same as
`Set.image_mono` but with a different argument order). Disabled to
force manual proof. -/
TheoremDoc Set.image_subset as "Set.image_subset" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_inter_subset Iff.rfl Set.image_mono Set.image_subset
