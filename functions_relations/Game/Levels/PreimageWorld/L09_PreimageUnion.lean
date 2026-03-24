import Game.Metadata

World "PreimageWorld"
Level 9

Title "Preimage Preserves Union"

TheoremTab "Set"

Introduction "
# Disjunction Passes Through

Preimage also distributes over union:

$$f^{-1}(s \\cup t) = f^{-1}(s) \\cup f^{-1}(t)$$

The reasoning is the same: `f x ∈ s ∪ t` means `f x ∈ s ∨ f x ∈ t`,
which is exactly `x ∈ f ⁻¹' s ∨ x ∈ f ⁻¹' t`, i.e., `x ∈ f ⁻¹' s ∪ f ⁻¹' t`.

The disjunction `∨` passes through just like conjunction did.

**Proof plan**:
1. `ext x` then `constructor`
2. **Forward**: `intro hx`, then case-split on `hx` with
   `cases hx with | inl hs | inr ht`, using `left`/`right`
3. **Backward**: symmetric
"

/-- Preimage distributes over union. -/
Statement (α β : Type) (f : α → β) (s t : Set β) :
    f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t := by
  Hint "Start with `ext x` then `constructor`."
  ext x
  constructor
  -- Forward: x ∈ f ⁻¹' (s ∪ t) → x ∈ f ⁻¹' s ∪ f ⁻¹' t
  · Hint "**Forward**: `x ∈ f ⁻¹' (s ∪ t)` means `f x ∈ s ∨ f x ∈ t`.
    Use `intro hx` then `cases hx with | inl hs | inr ht` to split."
    Hint (hidden := true) "After `intro hx` and `cases`:
    - `inl` case: `left; exact hs`
    - `inr` case: `right; exact ht`"
    intro hx
    Hint "Now case-split on the disjunction:
    `cases hx with | inl hs | inr ht`."
    cases hx with
    | inl hs =>
    Hint "`hs : f x ∈ s`, so `x ∈ f ⁻¹' s`. Use `left`."
    left
    exact hs
    | inr ht =>
    Hint "`ht : f x ∈ t`, so `x ∈ f ⁻¹' t`. Use `right`."
    right
    exact ht
  -- Backward: x ∈ f ⁻¹' s ∪ f ⁻¹' t → x ∈ f ⁻¹' (s ∪ t)
  · Hint "**Backward**: case-split on the union hypothesis."
    Hint (hidden := true) "`intro hx` then `cases hx with | inl hs | inr ht`.
    In each case, use `left`/`right` then `exact`."
    intro hx
    cases hx with
    | inl hs =>
    Hint "`hs : x ∈ f ⁻¹' s`, i.e., `f x ∈ s`. Use `left` to target the left disjunct."
    left
    exact hs
    | inr ht =>
    Hint "`ht : x ∈ f ⁻¹' t`, i.e., `f x ∈ t`. Use `right` to target the right disjunct."
    right
    exact ht

Conclusion "
You proved `f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t`. The proof used
case analysis with `cases` and `left`/`right` — the same moves
you used for union in Set Operations World.

**Scoreboard so far**:

| Set operation | Preimage distributes? | Why? |
|---|---|---|
| `∩` (intersection) | Yes: `f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t` | `∧` passes through |
| `∪` (union) | Yes: `f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t` | `∨` passes through |

Next: complement. Does `¬` also pass through?

The library name is `Set.preimage_union`.
"

/-- `Set.preimage_union` states `f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t`. -/
TheoremDoc Set.preimage_union as "Set.preimage_union" in "Set"

NewTheorem Set.preimage_union

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith rfl
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.preimage_union Iff.rfl
