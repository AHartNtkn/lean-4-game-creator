import Game.Metadata

World "PreimageWorld"
Level 5

Title "Preimage Preserves Subsets"

TheoremTab "Set"

Introduction "
# Preimage Is Monotone

If `s ⊆ t`, then `f ⁻¹' s ⊆ f ⁻¹' t`. In words: if a target set
grows, the preimage grows too.

Why? If `x` maps into `s` (a subset of `t`), then `x` certainly maps
into `t`.

This is your first abstract preimage proof — the function `f` is
no longer a specific function like `n ↦ n + 1`, but an arbitrary
function.

**Proof plan**:
1. `intro x hx` — start the subset proof
2. Now `hx : x ∈ f ⁻¹' s`, which is definitionally `f x ∈ s`
3. The subset hypothesis `h : s ⊆ t` is a function: given `f x ∈ s`,
   it produces `f x ∈ t`
4. Apply `h` to `hx` to get `f x ∈ t`, which is `x ∈ f ⁻¹' t`
"

/-- If s ⊆ t then f ⁻¹' s ⊆ f ⁻¹' t. -/
Statement (α β : Type) (f : α → β) (s t : Set β) (h : s ⊆ t) :
    f ⁻¹' s ⊆ f ⁻¹' t := by
  Hint "Start with `intro x hx` as in every subset proof."
  intro x hx
  Hint "`hx` says `x ∈ f ⁻¹' s`, which is definitionally `f x ∈ s`.
  The hypothesis `h : s ⊆ t` says `∀ y, y ∈ s → y ∈ t`. Apply `h`
  to `hx` — Lean can see that `hx : f x ∈ s`."
  Hint (hidden := true) "`apply h` reduces the goal to `f x ∈ s`.
  Then `exact hx` closes it.

  Alternatively, `exact h hx` does both steps at once."
  Branch
    apply h
    exact hx
  Branch
    rw [Set.mem_preimage] at hx
    rw [Set.mem_preimage]
    exact h hx
  exact h hx

Conclusion "
You proved preimage monotonicity: bigger target set → bigger preimage.

The proof was just two steps: `intro x hx`, then `exact h hx`.
This works because:

1. `hx : x ∈ f ⁻¹' s` is definitionally `f x ∈ s`
2. `h : s ⊆ t` accepts any element of `s`, including `f x`
3. `h hx : f x ∈ t` is definitionally `x ∈ f ⁻¹' t`

Notice how Lean's definitional transparency makes preimage proofs
short — the function application is invisible. The proof reads exactly
like the mathematical argument: \"If `f x ∈ s` and `s ⊆ t`, then
`f x ∈ t`.\"

The library name for this fact is `Set.preimage_mono`.
"

/-- `Set.preimage_mono` states `s ⊆ t → f ⁻¹' s ⊆ f ⁻¹' t`. -/
TheoremDoc Set.preimage_mono as "Set.preimage_mono" in "Set"

NewTheorem Set.preimage_mono

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.preimage_mono
