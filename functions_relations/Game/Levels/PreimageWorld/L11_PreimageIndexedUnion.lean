import Game.Metadata

World "PreimageWorld"
Level 11

Title "Preimage Preserves Indexed Union"

TheoremTab "Set"

Introduction "
# Existentials Pass Through Too

You proved that preimage preserves binary union:
`f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t`. The logical reason was that
`∨` passes through function application.

Indexed union generalizes binary union from `∨` to `∃`:
`x ∈ ⋃ i, s i` means `∃ i, x ∈ s i`. Does preimage preserve
this too?

$$f^{-1}\\!\\left(\\bigcup_i s_i\\right) = \\bigcup_i f^{-1}(s_i)$$

Yes — for the same reason. The left side says `∃ i, f x ∈ s i`,
and the right side says `∃ i, x ∈ f ⁻¹' (s i)`, which is also
`∃ i, f x ∈ s i`. The existential quantifier passes through
function application unchanged.

**A change in proof technique**: Unlike binary intersection and
union (which unfold definitionally), indexed union membership
`x ∈ ⋃ i, s i ↔ ∃ i, x ∈ s i` requires an explicit rewrite with
`Set.mem_iUnion`. This is because indexed union (`⋃`) is defined
differently from binary union (`∪`) in Lean — the indexed version
uses a more general construction that does not reduce by
definitional unfolding.

**Proof plan**:
1. `ext x` then `constructor`
2. **Forward**: The hypothesis is a preimage membership. Use
   `rw [Set.mem_preimage]` to unwrap it, then `rw [Set.mem_iUnion]`
   to expose the `∃`. Destructure and reassemble.
3. **Backward**: The hypothesis is an indexed union. Use
   `rw [Set.mem_iUnion]` directly, destructure, then reassemble
   with `rw [Set.mem_preimage]` and `rw [Set.mem_iUnion]`.
"

/-- `preimage_iUnion` states `f ⁻¹' (⋃ i, s i) = ⋃ i, f ⁻¹' (s i)`.

## When to use it
When you need to distribute a preimage over an indexed union.
The existential quantifier passes through function application.

## Example
If `f : α → β` and `s : ι → Set β`, then
`f ⁻¹' (⋃ i, s i) = ⋃ i, f ⁻¹' (s i)`.
-/
TheoremDoc preimage_iUnion as "preimage_iUnion" in "Set"

/-- `Set.preimage_iUnion` is the Mathlib version of `preimage_iUnion`. -/
TheoremDoc Set.preimage_iUnion as "Set.preimage_iUnion" in "Set"

/-- Preimage distributes over indexed union. -/
Statement preimage_iUnion (α β ι : Type) (f : α → β) (s : ι → Set β) :
    f ⁻¹' (⋃ i, s i) = ⋃ i, f ⁻¹' (s i) := by
  Hint "Start with `ext x` then `constructor`."
  ext x
  constructor
  -- Forward: x ∈ f ⁻¹' (⋃ i, s i) → x ∈ ⋃ i, f ⁻¹' (s i)
  · Hint "**Forward**: The hypothesis `hx` is `x ∈ f ⁻¹' (⋃ i, s i)`.
    First unwrap the preimage with `rw [Set.mem_preimage] at hx`
    to get `f x ∈ ⋃ i, s i`. Then `rw [Set.mem_iUnion] at hx`
    to expose `∃ i, f x ∈ s i`."
    Hint (hidden := true) "`intro hx` then `rw [Set.mem_preimage] at hx`
    then `rw [Set.mem_iUnion] at hx` then `obtain ⟨i, hi⟩ := hx`
    then `rw [Set.mem_iUnion]` then `exact ⟨i, hi⟩`."
    intro hx
    Hint "Unwrap the preimage: `rw [Set.mem_preimage] at hx`."
    rw [Set.mem_preimage] at hx
    Hint "Now `hx : f x ∈ ⋃ i, s i`. Expose the existential:
    `rw [Set.mem_iUnion] at hx`."
    rw [Set.mem_iUnion] at hx
    Hint "Destructure: `obtain ⟨i, hi⟩ := hx` to get the witness `i`
    and `hi : f x ∈ s i`."
    obtain ⟨i, hi⟩ := hx
    Hint "Build the goal: `rw [Set.mem_iUnion]` then `exact ⟨i, hi⟩`."
    rw [Set.mem_iUnion]
    exact ⟨i, hi⟩
  -- Backward: x ∈ ⋃ i, f ⁻¹' (s i) → x ∈ f ⁻¹' (⋃ i, s i)
  · Hint "**Backward**: Same structure — unpack, find the witness,
    reassemble."
    Hint (hidden := true) "`intro hx` then `rw [Set.mem_iUnion] at hx`
    then `obtain ⟨i, hi⟩ := hx` then `rw [Set.mem_preimage]`
    then `rw [Set.mem_iUnion]` then `exact ⟨i, hi⟩`."
    intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    Hint "Now build the preimage membership. Use `rw [Set.mem_preimage]`
    then `rw [Set.mem_iUnion]` then `exact ⟨i, hi⟩`."
    rw [Set.mem_preimage]
    rw [Set.mem_iUnion]
    exact ⟨i, hi⟩

Conclusion "
You proved `f ⁻¹' (⋃ i, s i) = ⋃ i, f ⁻¹' (s i)`. The proof
was the same destructure-reassemble pattern as the binary case,
with `rw [Set.mem_iUnion]` replacing the automatic unfolding and
`rw [Set.mem_preimage]` unwrapping the preimage layer.

The existential `∃ i, f x ∈ s i` passes through function application
just as `∨` did. Both directions used the same witness `i` — no
information was lost.

Compare with the binary case:

| | Binary | Indexed |
|---|---|---|
| Operation | `s ∪ t` | `⋃ i, s i` |
| Logic | `∨` | `∃` |
| Proof move | `cases`/`left`/`right` | `obtain`/`use` |
| Preimage preserves? | Yes | Yes |

The theorem name in this game is `preimage_iUnion`. (Mathlib does
not have a standalone theorem by this name — the result follows
from `simp` with indexed union lemmas. We name it explicitly so
you can reference it.)
"

NewTheorem preimage_iUnion

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith rfl
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.preimage_iUnion Iff.rfl
