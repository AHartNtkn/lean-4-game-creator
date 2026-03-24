import Game.Metadata

World "PreimageWorld"
Level 7

Title "Preimage of the Universal Set"

TheoremTab "Set"

Introduction "
# Everything Maps Into Everything

What is `f ⁻¹' Set.univ`? For any `x`, `f x ∈ Set.univ` is `True`
(since everything is in `Set.univ`). So every `x` qualifies, and
`f ⁻¹' Set.univ = Set.univ`.

This is the companion to the empty set case. Together they say:
- `f ⁻¹' ∅ = ∅` — nothing maps into nothing
- `f ⁻¹' Set.univ = Set.univ` — everything maps into everything

**Proof plan**:
1. `ext x` then `constructor`
2. Both directions: `intro _; constructor` (since `True` is the goal
   and `constructor` closes `True`)
"

/-- The preimage of the universal set is universal. -/
Statement (α β : Type) (f : α → β) : f ⁻¹' Set.univ = Set.univ := by
  Hint "Start with `ext x` then `constructor`."
  ext x
  constructor
  · Hint "**Forward**: `x ∈ f ⁻¹' Set.univ` implies `x ∈ Set.univ`.
    The goal is `True` (since `x ∈ Set.univ` unfolds to `True`).
    Use `intro _` to discard the hypothesis, then `constructor`."
    Hint (hidden := true) "`intro _` then `constructor`."
    intro _
    constructor
  · Hint "**Backward**: `x ∈ Set.univ` implies `x ∈ f ⁻¹' Set.univ`.
    The hypothesis unfolds to `True` and the goal unfolds to `True`.
    Use `intro _` then `constructor`."
    Hint (hidden := true) "`intro _` then `constructor`."
    intro _
    constructor

Conclusion "
You proved `f ⁻¹' Set.univ = Set.univ`. Both sides reduce to `True`.

**Boundary cases summarized**:
| Target set | Preimage | Reason |
|---|---|---|
| `∅` | `∅` | `f x ∈ ∅` is `False` for all `x` |
| `Set.univ` | `Set.univ` | `f x ∈ Set.univ` is `True` for all `x` |

As with the empty set, the two sides are definitionally equal —
both reduce to `{_ | True}`. The `ext` + `constructor` proof makes
this definitional equality explicit.

The library name is `Set.preimage_univ`.

**Looking ahead**: The next levels show that preimage preserves
intersection, union, and complement. This is the central fact about
preimages: they commute with ALL set operations.
"

/-- `Set.preimage_univ` states `f ⁻¹' Set.univ = Set.univ`. -/
TheoremDoc Set.preimage_univ as "Set.preimage_univ" in "Set"

NewTheorem Set.preimage_univ

/-- `Set.eq_univ_iff_forall` states `s = Set.univ ↔ ∀ x, x ∈ s`.
Disabled to prevent one-shotting the preimage-univ proof. -/
TheoremDoc Set.eq_univ_iff_forall as "Set.eq_univ_iff_forall" in "Set"

/-- `Set.eq_univ_of_forall` states that if `∀ x, x ∈ s` then `s = Set.univ`.
Disabled to prevent one-shotting the preimage-univ proof. -/
TheoremDoc Set.eq_univ_of_forall as "Set.eq_univ_of_forall" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith rfl
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.preimage_univ Set.eq_univ_iff_forall Set.eq_univ_of_forall Iff.rfl
