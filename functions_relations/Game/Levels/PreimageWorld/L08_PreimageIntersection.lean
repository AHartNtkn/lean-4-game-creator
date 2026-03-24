import Game.Metadata

World "PreimageWorld"
Level 8

Title "Preimage Preserves Intersection"

TheoremTab "Set"

Introduction "
# Conjunction Passes Through

Here is the first major structural result: preimage distributes over
intersection.

$$f^{-1}(s \\cap t) = f^{-1}(s) \\cap f^{-1}(t)$$

Why? An element `x` is in the left side when `f x ∈ s ∩ t`, which
means `f x ∈ s ∧ f x ∈ t`. The right side says `x ∈ f ⁻¹' s` and
`x ∈ f ⁻¹' t`, which means `f x ∈ s` and `f x ∈ t`. These are the
same condition!

The conjunction `∧` passes through function application unchanged.
This is the reason preimage \"preserves\" intersection.

**Proof plan**:
1. `ext x` — reduce to membership
2. `constructor` — split the `↔`
3. **Forward**: `intro hx`, destructure with `obtain`, reassemble
4. **Backward**: same in reverse
"

/-- Preimage distributes over intersection. -/
Statement (α β : Type) (f : α → β) (s t : Set β) :
    f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t := by
  Hint "Start with `ext x` then `constructor`."
  ext x
  constructor
  -- Forward: x ∈ f ⁻¹' (s ∩ t) → x ∈ f ⁻¹' s ∩ f ⁻¹' t
  · Hint "**Forward**: `x ∈ f ⁻¹' (s ∩ t)` means `f x ∈ s ∩ t`,
    which is `f x ∈ s ∧ f x ∈ t`. Destructure with `obtain`."
    Hint (hidden := true) "`intro hx` then `obtain ⟨hs, ht⟩ := hx`
    then `exact ⟨hs, ht⟩`."
    intro hx
    Hint "Destructure `hx` into its two components with
    `obtain ⟨hs, ht⟩ := hx`."
    obtain ⟨hs, ht⟩ := hx
    Hint "Now `hs : f x ∈ s` and `ht : f x ∈ t`. Build the
    conjunction with `exact ⟨hs, ht⟩`."
    exact ⟨hs, ht⟩
  -- Backward: x ∈ f ⁻¹' s ∩ f ⁻¹' t → x ∈ f ⁻¹' (s ∩ t)
  · Hint "**Backward**: destructure the intersection hypothesis
    and reassemble."
    Hint (hidden := true) "`intro hx` then `obtain ⟨hs, ht⟩ := hx`
    then `exact ⟨hs, ht⟩`."
    intro hx
    obtain ⟨hs, ht⟩ := hx
    exact ⟨hs, ht⟩

Conclusion "
You proved `f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t`. Both directions
were identical: destructure, reassemble.

**Why both directions are the same**: The conjunction `f x ∈ s ∧ f x ∈ t`
IS both sides. There is no rearrangement, no extra condition, no
information loss. The `∧` passes through `f` unchanged.

**The definitional tautology pattern**: When both sides of a `↔` are
definitionally equal, each direction reduces to `intro hx; exact hx` —
you introduce the hypothesis and hand it right back. Call this a
**definitional tautology**: the proof is trivial because the two sides
ARE the same proposition, just written differently. You saw this in the
`∅` and `univ` cases, and you will see it again in the complement,
composition, and identity cases. When you notice both directions are
the same proof, it means the two sides are the same proposition under
definitional unfolding. We will use the term \"definitional tautology\"
to refer to this pattern going forward.

Contrast this with what happens for **images** (which you will see
later): `f '' (s ∩ t) ⊆ f '' s ∩ f '' t` is only a
subset, NOT an equality. Image involves an existential `∃ x ∈ s,
f x = y`, and `∃` does NOT distribute over `∧` in general. This
asymmetry between image and preimage is a central theme of this
course.

**Concrete counterexample**: Let `f n = 0` (constant function),
`s = {0}`, `t = {1}`. Then `f '' s = {0}` and `f '' t = {0}`,
so `f '' s ∩ f '' t = {0}`. But `s ∩ t = ∅`, so
`f '' (s ∩ t) = ∅`. The image of the intersection is strictly
smaller than the intersection of the images. No such failure
happens for preimage — you just proved it.

The library name is `Set.preimage_inter`.
"

/-- `Set.preimage_inter` states `f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t`. -/
TheoremDoc Set.preimage_inter as "Set.preimage_inter" in "Set"

NewTheorem Set.preimage_inter

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith rfl
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.preimage_inter Iff.rfl
