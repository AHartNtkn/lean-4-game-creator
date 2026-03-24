import Game.Metadata

World "PreimageWorld"
Level 6

Title "Preimage of the Empty Set"

TheoremTab "Set"

Introduction "
# Nothing Maps Into Nothing

What is the preimage of the empty set? If `t = ∅`, then `f ⁻¹' ∅`
is the set of all `x` such that `f x ∈ ∅`. But nothing is in `∅`,
so no `x` qualifies. Therefore `f ⁻¹' ∅ = ∅`.

This is a set equality, so the natural approach is `ext` + `constructor`.

**Proof plan**:
1. `ext x` — reduce to membership biconditional
2. `constructor` — split the `↔`
3. **Forward**: `x ∈ f ⁻¹' ∅` means `f x ∈ ∅`, which is `False`. So
   `intro hx; exact hx` (an assumption of `False` closes any goal).
4. **Backward**: `x ∈ ∅` is also `False`. Same idea.
"

/-- The preimage of the empty set is empty. -/
Statement (α β : Type) (f : α → β) : f ⁻¹' ∅ = ∅ := by
  Hint "Start with `ext x` to reduce to element-wise membership."
  ext x
  Hint "The goal is `x ∈ f ⁻¹' ∅ ↔ x ∈ ∅`. Both sides unfold to
  `False` (since nothing is in `∅`). Use `constructor` to split."
  constructor
  · Hint "**Forward**: `x ∈ f ⁻¹' ∅` is definitionally `f x ∈ ∅`,
    which is `False`. Introducing this gives a proof of `False`,
    which closes any goal."
    Hint (hidden := true) "`intro hx` then `exact hx`."
    intro hx
    exact hx
  · Hint "**Backward**: `x ∈ ∅` is also `False`. Same argument."
    Hint (hidden := true) "`intro hx` then `exact hx`."
    intro hx
    exact hx

Conclusion "
You proved `f ⁻¹' ∅ = ∅`. Both directions reduced to `False → False`,
which is trivially true.

**Why this is definitional**: `x ∈ f ⁻¹' ∅` means `f x ∈ ∅`, and
`∅` is `{_ | False}`, so `f x ∈ ∅` IS `False`. Similarly, `x ∈ ∅`
IS `False`. The two sides are literally the same proposition. The
`ext` + `constructor` proof makes this definitional equality explicit
step by step.

**A note on `rfl`**: In real Lean code, `ext x; rfl` would close
this goal in one line, since both sides are definitionally equal.
We disable `rfl` in these set equality levels so you can see the
definitional unfolding step by step — understanding WHY the two sides are equal
is more valuable than closing the goal quickly.

The library name is `Set.preimage_empty`.
"

/-- `Set.preimage_empty` states `f ⁻¹' ∅ = ∅`. -/
TheoremDoc Set.preimage_empty as "Set.preimage_empty" in "Set"

NewTheorem Set.preimage_empty

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith rfl
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.preimage_empty Iff.rfl
