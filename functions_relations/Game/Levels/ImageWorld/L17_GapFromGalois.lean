import Game.Metadata

World "ImageWorld"
Level 17

Title "The Image-Preimage Gap from the Galois Connection"

TheoremTab "Set"

Introduction "
# Re-Deriving the Image-Preimage Gap

In Level 16, you re-derived image monotonicity from the Galois
connection. The conclusion hinted that the same technique also
re-derives the image-preimage gap `f '' (f ⁻¹' t) ⊆ t` (Level 14).

Now you will carry out this derivation yourself.

The idea is beautiful in its simplicity:
1. The Galois connection says `f '' s ⊆ t ↔ s ⊆ f ⁻¹' t`. With
   `s := f ⁻¹' t`, showing `f '' (f ⁻¹' t) ⊆ t` reduces to
   `f ⁻¹' t ⊆ f ⁻¹' t`.
2. But `f ⁻¹' t ⊆ f ⁻¹' t` is trivially true -- any set is a
   subset of itself!

Two key results of this world -- monotonicity (Level 16) and the
image-preimage gap (this level) -- are both immediate consequences
of the Galois connection. The adjunction is the engine; individual
results are free corollaries.

**Important**: As in Level 16, `rintro`, `rcases`, `obtain`, and
`cases` are disabled. You must use the Galois connection.

**Proof plan**:
1. `apply Set.image_subset_iff.mpr` -- apply the backward direction
   of the Galois connection
2. Close `f ⁻¹' t ⊆ f ⁻¹' t` with `intro x hx` then `exact hx`
"

/-- The image-preimage gap re-derived from the Galois connection. -/
Statement (α β : Type) (f : α → β) (t : Set β) :
    f '' (f ⁻¹' t) ⊆ t := by
  Hint "Use `apply Set.image_subset_iff.mpr` to apply the backward
  direction of the Galois connection. This transforms the goal
  `f '' (f ⁻¹' t) ⊆ t` into `f ⁻¹' t ⊆ f ⁻¹' t`."
  Hint (hidden := true) "`apply Set.image_subset_iff.mpr` then
  `intro x hx` and `exact hx`."
  apply Set.image_subset_iff.mpr
  Hint "The goal is now `f ⁻¹' t ⊆ f ⁻¹' t`. Any set is a subset
  of itself! Use `intro x hx` then `exact hx`."
  Hint (hidden := true) "`intro x hx` then `exact hx`."
  intro x hx
  exact hx

Conclusion "
The proof was just three steps:
1. `apply Set.image_subset_iff.mpr` -- Galois connection
2. `intro x hx` -- take an element
3. `exact hx` -- reflexivity

Compare with the direct proof (Level 14):
```
rintro y ⟨x, hx, rfl⟩
exact hx
```

Both proofs are short, but the Galois proof is more illuminating:
it shows WHY `f '' (f ⁻¹' t) ⊆ t` holds. The Galois connection
reduces it to a trivially true statement. No witnesses, no
existentials, no destructuring -- just one apply.

**The unifying principle**: In Level 16, you proved monotonicity
from the Galois connection. Here, you proved the image-preimage
gap from the same Galois connection. Both results are free
corollaries of the adjunction `f '' s ⊆ t ↔ s ⊆ f ⁻¹' t`.

This is a general pattern in mathematics: once you establish an
adjunction (Galois connection) between two operations, many
individual results become trivial consequences. The adjunction
is the deep fact; the results are surface phenomena.
"

/-- `Set.image_preimage_subset` states `f '' (f ⁻¹' t) ⊆ t`. Applying
the function to the preimage gives back a subset of the original.
Disabled here to force re-derivation from the Galois connection. -/
TheoremDoc Set.image_preimage_subset as "Set.image_preimage_subset" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr rintro rcases obtain cases
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_preimage_subset
