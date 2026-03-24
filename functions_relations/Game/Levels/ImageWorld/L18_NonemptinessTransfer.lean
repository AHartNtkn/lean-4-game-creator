import Game.Metadata

World "ImageWorld"
Level 18

Title "Image Preserves Nonemptiness"

TheoremTab "Set"

Introduction "
# Nonemptiness Transfers Through Images

If a set `s` is nonempty, then its image `f '' s` is also nonempty.
This is intuitively obvious: if there is an element in `s`, applying
`f` to it produces an element in `f '' s`.

In Lean, `Set.Nonempty s` means `∃ x, x ∈ s` -- there exists at
least one element. The proof pattern is different from the subset
and equality proofs you have been doing: instead of `ext`/`constructor`,
you destructure the nonemptiness hypothesis to get a witness, then
build image membership from that witness.

**Proof plan**:
1. `obtain ⟨x, hx⟩ := h` -- extract the witness from `Set.Nonempty s`
2. Construct `Set.Nonempty (f '' s)` using `f x` as the witness
"

/-- If s is nonempty, then f '' s is nonempty. -/
Statement (α β : Type) (f : α → β) (s : Set α) (h : Set.Nonempty s) :
    Set.Nonempty (f '' s) := by
  Hint "`h : Set.Nonempty s` means `∃ x, x ∈ s`. Destructure it
  with `obtain ⟨x, hx⟩ := h` to get a witness `x ∈ s`."
  Hint (hidden := true) "`obtain ⟨x, hx⟩ := h` then
  `exact ⟨f x, x, hx, rfl⟩`."
  obtain ⟨x, hx⟩ := h
  Hint "Now you have `x : α` and `hx : x ∈ s`. The goal is
  `Set.Nonempty (f '' s)`, which means `∃ y, y ∈ f '' s`.

  The witness is `f x`. It is in `f '' s` because `x ∈ s`."
  Hint (hidden := true) "`exact ⟨f x, x, hx, rfl⟩`

  The outer `⟨f x, ...⟩` provides the nonemptiness witness.
  The inner `x, hx, rfl` proves `f x ∈ f '' s`."
  Branch
    use f x
    exact ⟨x, hx, rfl⟩
  exact ⟨f x, x, hx, rfl⟩

Conclusion "
You proved `Set.Nonempty s → Set.Nonempty (f '' s)` -- image
preserves nonemptiness.

The proof was just two steps:
1. `obtain ⟨x, hx⟩ := h` -- extract the witness
2. `exact ⟨f x, x, hx, rfl⟩` -- repackage it as image membership

**A different proof shape**: This is NOT an `ext`/`constructor` proof
like the set equality and subset proofs you have been doing. Instead,
it is a direct existential construction: get an element, transform it,
show the result is in the image.

**The converse also holds**: If `f '' s` is nonempty, then `s` must
be nonempty. Why? Any element of `f '' s` has a witness `x ∈ s`
(by definition of image membership), so `s` contains at least `x`.
This means nonemptiness gives a biconditional: `Set.Nonempty s ↔
Set.Nonempty (f '' s)`. Unlike intersection (where only ⊆ held),
nonemptiness transfers in both directions unconditionally.

**Contrast with preimage**: Preimage ALSO preserves nonemptiness
(if `t` is nonempty and intersects the range, then `f ⁻¹' t` is
nonempty), but that requires additional conditions. Image preserves
nonemptiness unconditionally -- because every element of `s` has an
output under `f`.

**Boss preparation**: The boss combines image membership construction,
destructuring, range reasoning, and preimage unfolding. This level
practices the existential construction skill in a new context.

The library name is `Set.Nonempty.image`.
"

/-- `Set.Nonempty.image` states that if `s` is nonempty, then `f '' s`
is nonempty. Image preserves nonemptiness unconditionally.

Disabled to force manual witness construction.
-/
TheoremDoc Set.Nonempty.image as "Set.Nonempty.image" in "Set"

NewTheorem Set.Nonempty.image

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.Nonempty.image
