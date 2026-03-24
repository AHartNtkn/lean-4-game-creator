import Game.Metadata

World "PreimageWorld"
Level 13

Title "Preimage Under the Identity"

TheoremTab "Set"

Introduction "
# The Identity Law

What happens when you take the preimage under the identity function?

$$\\text{id}^{-1}(s) = s$$

Since `id x = x`, membership `x \\in \\text{id}^{-1}(s)` is just
`id x \\in s`, which is `x \\in s`. The preimage is the set itself.

This is a **definitional tautology** (Level 8): both sides reduce to
the same proposition, so each direction of the proof is
`intro hx; exact hx`.

Combined with the composition result in the next level
(`(g . f) ⁻¹' t = f ⁻¹' (g ⁻¹' t)`), this establishes that
preimage satisfies the two **functor laws**:
1. **Identity**: `id ⁻¹' s = s`
2. **Composition**: `(g . f) ⁻¹' s = f ⁻¹' (g ⁻¹' s)`

These are exactly the axioms that make preimage a
**contravariant functor** from sets of outputs to sets of inputs.

**Proof plan**:
1. `ext x` then `constructor`
2. Both directions: `intro hx; exact hx`
"

/-- `Set.preimage_id` states `id ⁻¹' s = s` — preimage under the
identity function returns the set unchanged.

## When to use it
When simplifying a preimage under `id`. Combined with `Set.preimage_comp`,
this establishes that preimage is a contravariant functor.

## Example
`id ⁻¹' {n | n < 5} = {n | n < 5}`
-/
TheoremDoc Set.preimage_id as "Set.preimage_id" in "Set"

/-- Preimage under the identity function is the set itself. -/
Statement (α : Type) (s : Set α) : id ⁻¹' s = s := by
  Hint "Start with `ext x` then `constructor`."
  ext x
  constructor
  · Hint "**Forward**: `x ∈ id ⁻¹' s` is definitionally `id x ∈ s`,
    which is `x ∈ s`. The hypothesis IS the goal."
    Hint (hidden := true) "`intro hx` then `exact hx`."
    intro hx
    exact hx
  · Hint "**Backward**: `x ∈ s` implies `x ∈ id ⁻¹' s` — same
    proposition."
    Hint (hidden := true) "`intro hx` then `exact hx`."
    intro hx
    exact hx

Conclusion "
Another definitional tautology: `id ⁻¹' s = s`. Both sides reduce
to `x ∈ s`, so the proof is `intro hx; exact hx` in both directions.

**The functor laws**: Preimage satisfies:
1. `id ⁻¹' s = s` (this level)
2. `(g . f) ⁻¹' s = f ⁻¹' (g ⁻¹' s)` (next level)

These are the defining properties of a **functor** — a structure-
preserving map between categories. Preimage is **contravariant**
because it reverses the direction of composition: `g . f` on
functions becomes `f⁻¹ . g⁻¹` on preimages (apply `g⁻¹` first,
then `f⁻¹`).

The library name is `Set.preimage_id`.
"

NewTheorem Set.preimage_id

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith rfl
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.preimage_id Iff.rfl
