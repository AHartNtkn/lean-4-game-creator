import Game.Metadata

World "PreimageWorld"
Level 12

Title "Preimage Preserves Indexed Intersection"

TheoremTab "Set"

Introduction "
# Universals Pass Through Too

Indexed intersection generalizes binary intersection from `∧` to `∀`:
`x ∈ ⋂ i, s i` means `∀ i, x ∈ s i`. Does preimage preserve this?

$$f^{-1}\\!\\left(\\bigcap_i s_i\\right) = \\bigcap_i f^{-1}(s_i)$$

Yes. The left side says `∀ i, f x ∈ s i`, and the right side says
`∀ i, x ∈ f ⁻¹' (s i)`, which is also `∀ i, f x ∈ s i`. Same
proposition.

**Proof plan**:
1. `ext x` then `constructor`
2. Each direction: `rw [Set.mem_preimage]` to unwrap preimage,
   `rw [Set.mem_iInter]` to expose the `∀`, then hand back
"

/-- `preimage_iInter` states `f ⁻¹' (⋂ i, s i) = ⋂ i, f ⁻¹' (s i)`.

## When to use it
When you need to distribute a preimage over an indexed intersection.
The universal quantifier passes through function application.

## Example
If `f : α → β` and `s : ι → Set β`, then
`f ⁻¹' (⋂ i, s i) = ⋂ i, f ⁻¹' (s i)`.
-/
TheoremDoc preimage_iInter as "preimage_iInter" in "Set"

/-- `Set.preimage_iInter` is the Mathlib version of `preimage_iInter`. -/
TheoremDoc Set.preimage_iInter as "Set.preimage_iInter" in "Set"

/-- Preimage distributes over indexed intersection. -/
Statement preimage_iInter (α β ι : Type) (f : α → β) (s : ι → Set β) :
    f ⁻¹' (⋂ i, s i) = ⋂ i, f ⁻¹' (s i) := by
  Hint "Start with `ext x` then `constructor`."
  ext x
  constructor
  -- Forward: x ∈ f ⁻¹' (⋂ i, s i) → x ∈ ⋂ i, f ⁻¹' (s i)
  · Hint "**Forward**: Unwrap the preimage with
    `rw [Set.mem_preimage] at hx`, then use `rw [Set.mem_iInter]`
    to expose `∀ i, f x ∈ s i`."
    Hint (hidden := true) "`intro hx` then `rw [Set.mem_preimage] at hx`
    then `rw [Set.mem_iInter] at hx` then `rw [Set.mem_iInter]`
    then `exact hx`."
    intro hx
    Hint "Unwrap: `rw [Set.mem_preimage] at hx`."
    rw [Set.mem_preimage] at hx
    Hint "Expose the universal: `rw [Set.mem_iInter] at hx` to get
    `hx : ∀ i, f x ∈ s i`."
    rw [Set.mem_iInter] at hx
    Hint "Now `rw [Set.mem_iInter]` on the goal, then `exact hx`."
    rw [Set.mem_iInter]
    exact hx
  -- Backward: x ∈ ⋂ i, f ⁻¹' (s i) → x ∈ f ⁻¹' (⋂ i, s i)
  · Hint "**Backward**: Same structure — unpack, hand back."
    Hint (hidden := true) "`intro hx` then `rw [Set.mem_iInter] at hx`
    then `rw [Set.mem_preimage]` then `rw [Set.mem_iInter]`
    then `exact hx`."
    intro hx
    rw [Set.mem_iInter] at hx
    rw [Set.mem_preimage]
    rw [Set.mem_iInter]
    exact hx

Conclusion "
You proved `f ⁻¹' (⋂ i, s i) = ⋂ i, f ⁻¹' (s i)`. The proof
was even simpler than the union case — the universal quantifier
`∀` passes through unchanged, and `exact hx` closes each direction
immediately after rewriting.

**Full scoreboard**:

| Operation | Logic | Preimage preserves? |
|---|---|---|
| `∩` | `∧` | Yes |
| `∪` | `∨` | Yes |
| `ᶜ` | `¬` | Yes |
| `⋂ i` | `∀ i` | Yes |
| `⋃ i` | `∃ i` | Yes |

Every logical connective — conjunction, disjunction, negation,
universal, existential — passes through function application.
This is why preimage preserves ALL set operations.

The theorem name in this game is `preimage_iInter`. (Like
`preimage_iUnion`, Mathlib handles this via `simp` rather than a
standalone theorem.)
"

NewTheorem preimage_iInter

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith rfl
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.preimage_iInter Iff.rfl
