import Game.Metadata

World "ImageWorld"
Level 19

Title "Nonemptiness Converse"

TheoremTab "Set"

Introduction "
# If the Image is Nonempty, So is the Source

In Level 18, you proved that if `s` is nonempty, then `f '' s` is
nonempty. The conclusion mentioned that the converse also holds.
Now you will prove it.

If `f '' s` is nonempty, there exists some `y ∈ f '' s`. By image
membership, there exists `x ∈ s` with `f x = y`. In particular,
`x ∈ s`, so `s` is nonempty.

This completes the biconditional: `Set.Nonempty s ↔
Set.Nonempty (f '' s)`. Nonemptiness transfers in both directions
unconditionally.

**Proof plan**:
1. `obtain ⟨y, hy⟩ := h` -- extract a witness from image nonemptiness
2. `obtain ⟨x, hx, rfl⟩ := hy` -- destructure image membership
3. `exact ⟨x, hx⟩` -- the source set contains `x`
"

/-- If f '' s is nonempty, then s is nonempty. -/
Statement (α β : Type) (f : α → β) (s : Set α) (h : Set.Nonempty (f '' s)) :
    Set.Nonempty s := by
  Hint "`h : Set.Nonempty (f '' s)` means there exists `y ∈ f '' s`.
  Destructure with `obtain ⟨y, hy⟩ := h` to get a witness."
  Hint (hidden := true) "`obtain ⟨y, hy⟩ := h` then
  `obtain ⟨x, hx, rfl⟩ := hy` then `exact ⟨x, hx⟩`."
  obtain ⟨y, hy⟩ := h
  Hint "`hy : y ∈ f '' s` means there exists `x ∈ s` with `f x = y`.
  Destructure with `obtain ⟨x, hx, rfl⟩ := hy`."
  obtain ⟨x, hx, rfl⟩ := hy
  Hint "Now `hx : x ∈ s`. The goal is `Set.Nonempty s`, which means
  there exists some element in `s`. The witness is `x`."
  Hint (hidden := true) "`exact ⟨x, hx⟩`"
  exact ⟨x, hx⟩

Conclusion "
You proved `Set.Nonempty (f '' s) → Set.Nonempty s` -- the converse
of Level 18.

Together with Level 18, this gives the full biconditional:
`Set.Nonempty s ↔ Set.Nonempty (f '' s)`.

**The proof pattern**: Nonemptiness of the image gives a witness
`y ∈ f '' s`. Image membership gives a preimage `x ∈ s`. So `s`
has an element.

**Compare with preimage**: Does `Set.Nonempty (f ⁻¹' t)` imply
`Set.Nonempty t`? YES -- if `x ∈ f ⁻¹' t`, then `f x ∈ t`.
But does `Set.Nonempty t` imply `Set.Nonempty (f ⁻¹' t)`? NOT
necessarily! If no element of `t` is in the range of `f`, then
`f ⁻¹' t = ∅` even though `t` is nonempty. So nonemptiness
of preimage requires the additional condition that `t` intersects
`Set.range f`.

**Boss preparation**: The boss combines image construction,
destructuring, range reasoning, and preimage unfolding.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem
