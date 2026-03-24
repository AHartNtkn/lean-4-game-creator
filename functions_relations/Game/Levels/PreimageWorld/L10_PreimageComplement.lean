import Game.Metadata

World "PreimageWorld"
Level 10

Title "Preimage Preserves Complement"

TheoremTab "Set"

Introduction "
# Negation Passes Through

$$f^{-1}(s^c) = (f^{-1}(s))^c$$

An element `x` is in `f ⁻¹' sᶜ` when `f x ∈ sᶜ`, i.e., `f x ∉ s`,
i.e., `¬(f x ∈ s)`. And `x ∈ (f ⁻¹' s)ᶜ` means `x ∉ f ⁻¹' s`,
i.e., `¬(f x ∈ s)`. Same proposition again!

**Proof plan**:
1. `ext x` then `constructor`
2. Both directions: the hypothesis IS the goal (definitionally)

This proof is especially short because negation, like conjunction
and disjunction, passes through function application unchanged.
"

/-- Preimage distributes over complement. -/
Statement (α β : Type) (f : α → β) (s : Set β) :
    f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ := by
  Hint "Start with `ext x` then `constructor`."
  ext x
  constructor
  · Hint "**Forward**: `x ∈ f ⁻¹' sᶜ` is definitionally `¬(f x ∈ s)`,
    and `x ∈ (f ⁻¹' s)ᶜ` is also `¬(f x ∈ s)`. They are the same."
    Hint (hidden := true) "`intro hx` then `exact hx`."
    intro hx
    exact hx
  · Hint "**Backward**: same reasoning — the two sides are
    definitionally equal."
    Hint (hidden := true) "`intro hx` then `exact hx`."
    intro hx
    exact hx

Conclusion "
You proved `f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ`. The proof was `intro hx; exact hx`
in both directions — the hypothesis is literally the goal each time.

**The pattern is now clear**: Preimage preserves every set operation
because it simply applies the function before checking membership.
The logical connective (`∧`, `∨`, `¬`) is untouched:

| Operation | Left side | Unfolds to | Right side | Unfolds to |
|---|---|---|---|---|
| `∩` | `f x ∈ s ∩ t` | `f x ∈ s ∧ f x ∈ t` | `x ∈ f⁻¹s ∩ f⁻¹t` | `f x ∈ s ∧ f x ∈ t` |
| `∪` | `f x ∈ s ∪ t` | `f x ∈ s ∨ f x ∈ t` | `x ∈ f⁻¹s ∪ f⁻¹t` | `f x ∈ s ∨ f x ∈ t` |
| `ᶜ` | `f x ∈ sᶜ` | `¬(f x ∈ s)` | `x ∈ (f⁻¹s)ᶜ` | `¬(f x ∈ s)` |

In each case, both sides reduce to the same proposition. Preimage is
just \"apply `f` first\" — it does not change the logical structure.

**Mathematically**: Preimage is a **homomorphism** from the Boolean
algebra of subsets of `β` to the Boolean algebra of subsets of `α`.
It preserves meets (`∩`), joins (`∪`), and complements (`ᶜ`).

The library name is `Set.preimage_compl`.
"

/-- `Set.preimage_compl` states `f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ`. -/
TheoremDoc Set.preimage_compl as "Set.preimage_compl" in "Set"

NewTheorem Set.preimage_compl

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith rfl
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.preimage_compl Iff.rfl
