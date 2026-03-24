import Game.Metadata

World "ImageWorld"
Level 15

Title "The Preimage-Image Gap"

TheoremTab "Set"

Introduction "
# Pulling Back Then Pushing Forward: s ⊆ f ⁻¹' (f '' s)

Now the other direction: start with a set `s` of inputs, push it
forward to get `f '' s`, then pull back to get `f ⁻¹' (f '' s)`.
Do you recover `s`?

You get AT LEAST `s` -- as a subset:

$$s \\subseteq f^{-1}(f(s))$$

The proof is direct: if `x ∈ s`, then `f x ∈ f '' s` (using `x`
as the witness), so `x ∈ f ⁻¹' (f '' s)`.

But equality can fail! The preimage of the image can be LARGER than
`s`. If `f x₁ = f x₂` for `x₁ ∈ s` and `x₂ ∉ s`, then `x₂` is
in `f ⁻¹' (f '' s)` even though `x₂ ∉ s`.

**Your task**: Prove the ⊆ direction.

**Proof plan**:
1. `intro x hx` -- start the subset proof
2. Construct image membership: `f x ∈ f '' s` using witness `⟨x, hx, rfl⟩`
"

/-- Every element of s maps to a value in f '' s. -/
Statement (α β : Type) (f : α → β) (s : Set α) :
    s ⊆ f ⁻¹' (f '' s) := by
  Hint "The goal is `s ⊆ f ⁻¹' (f '' s)`. Start with `intro x hx`."
  Hint (hidden := true) "After `intro x hx`, the goal is
  `x ∈ f ⁻¹' (f '' s)`, which is `f x ∈ f '' s`. Construct the
  image membership: `exact ⟨x, hx, rfl⟩`."
  intro x hx
  Hint "The goal is `x ∈ f ⁻¹' (f '' s)`. By preimage membership,
  this means `f x ∈ f '' s`. You need to show there exists some
  element in `s` that maps to `f x`.

  The witness is `x` itself! Use `exact ⟨x, hx, rfl⟩`."
  Hint (hidden := true) "Alternatively: `use x` (Lean automatically
  verifies `hx : x ∈ s` and `f x = f x` by `rfl`)."
  Branch
    use x
  exact ⟨x, hx, rfl⟩

Conclusion "
The proof was just `intro x hx` then `exact ⟨x, hx, rfl⟩`.
Constructing image membership with the same element you started with.

**Why equality fails**: The reverse `f ⁻¹' (f '' s) ⊆ s` would
require: if `f x ∈ f '' s`, then `x ∈ s`. But `f x ∈ f '' s` only
means there exists SOME `x' ∈ s` with `f x' = f x`. If `f` is not
injective, `x'` might differ from `x`, and `x` might not be in `s`.

**When does equality hold?** If `f` is INJECTIVE: `f x' = f x`
implies `x' = x`, so `x' ∈ s` gives `x ∈ s`. You will prove this
in the problem set.

**Summary of the two gaps**:

| Statement | Holds? | Equality requires |
|---|---|---|
| `f '' (f ⁻¹' t) ⊆ t` | Always | Surjectivity onto `t` |
| `s ⊆ f ⁻¹' (f '' s)` | Always | Injectivity of `f` |

The image-preimage gap and the preimage-image gap are controlled by
different properties of `f`. This asymmetry is one of the central
insights of this course.

The library name is `Set.subset_preimage_image`.
"

/-- `Set.subset_preimage_image` states `s ⊆ f ⁻¹' (f '' s)`. Every
element of `s` is in the preimage of the image -- the preimage-image
roundtrip never loses elements, but it may gain extras. -/
TheoremDoc Set.subset_preimage_image as "Set.subset_preimage_image" in "Set"

NewTheorem Set.subset_preimage_image

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.subset_preimage_image
