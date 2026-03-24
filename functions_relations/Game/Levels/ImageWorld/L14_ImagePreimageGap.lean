import Game.Metadata

World "ImageWorld"
Level 14

Title "The Image-Preimage Gap"

TheoremTab "Set"

Introduction "
# Applying f Then Pulling Back: f '' (f ⁻¹' t) ⊆ t

What happens when you take a preimage and then push it forward?

Starting with a set `t` of outputs, `f ⁻¹' t` collects all inputs
that map into `t`. Then `f '' (f ⁻¹' t)` pushes those inputs
forward again. Do you get `t` back?

Almost -- but only a SUBSET:

$$f(f^{-1}(t)) \\subseteq t$$

The ⊆ direction is immediate: if `y ∈ f '' (f ⁻¹' t)`, there exists
`x ∈ f ⁻¹' t` with `f x = y`. Since `x ∈ f ⁻¹' t` means `f x ∈ t`,
and `y = f x`, we get `y ∈ t`.

But equality can fail! Elements of `t` that are NOT in the range of
`f` get \"lost\" -- there is no input that maps to them, so they
cannot appear in `f '' (f ⁻¹' t)`.

**Your task**: Prove the ⊆ direction.

**Proof plan**:
1. `rintro y ⟨x, hx, rfl⟩` -- destructure image membership
2. `hx` is already the answer!
"

/-- Pushing forward a preimage gives a subset of the original. -/
Statement (α β : Type) (f : α → β) (t : Set β) :
    f '' (f ⁻¹' t) ⊆ t := by
  Hint "Use `rintro y ⟨x, hx, rfl⟩` to destructure the image membership."
  Hint (hidden := true) "After destructuring, `hx : x ∈ f ⁻¹' t`,
  which is definitionally `f x ∈ t`. And the goal is `f x ∈ t`.
  So `exact hx` closes the proof."
  Branch
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hx
  rintro y ⟨x, hx, rfl⟩
  Hint "After `rintro`, you have `hx : x ∈ f ⁻¹' t`. Recall from
  Preimage World that `x ∈ f ⁻¹' t` is definitionally `f x ∈ t`.
  The goal is `f x ∈ t`. So `hx` IS the goal!"
  Hint (hidden := true) "`exact hx`"
  exact hx

Conclusion "
The proof was just two steps:
1. `rintro y ⟨x, hx, rfl⟩`
2. `exact hx`

That is because `hx : x ∈ f ⁻¹' t` IS `f x ∈ t` by definition.
The preimage membership unfolds directly to the goal.

**Why equality fails**: The reverse inclusion `t ⊆ f '' (f ⁻¹' t)`
requires: for every `y ∈ t`, find `x` with `f x = y`. But `y`
might not be in the range of `f`! If no input maps to `y`, there
is no witness.

**When does equality hold?** If every element of `t` IS in the range
of `f` -- i.e., if `t ⊆ Set.range f`. In the boss level, you will
prove this equality under exactly this condition.

**Foreshadowing**: If `f` is surjective (`Set.range f = Set.univ`),
then `t ⊆ Set.range f` holds automatically for every `t`, and
`f '' (f ⁻¹' t) = t` always.

The library name is `Set.image_preimage_subset`.
"

/-- `Set.image_preimage_subset` states `f '' (f ⁻¹' t) ⊆ t`. Applying
the function to the preimage gives back a subset of the original. -/
TheoremDoc Set.image_preimage_subset as "Set.image_preimage_subset" in "Set"

NewTheorem Set.image_preimage_subset

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_preimage_subset
