import Game.Metadata

World "SetOpsWorld"
Level 11

Title "Union Commutativity (Full Equality)"

TheoremTab "Set"

Introduction "
# s ∪ t = t ∪ s

In Level 10, you proved the element-level version: `x ∈ s ∪ t → x ∈ t ∪ s`.
The conclusion mentioned that combining this with `ext` gives the full
set equality. Now prove it!

$$s \\cup t = t \\cup s$$

**Proof plan**:
1. `ext x` — reduce to `x ∈ s ∪ t ↔ x ∈ t ∪ s`
2. `constructor` — split the biconditional
3. Each direction is exactly the Level 10 argument: case-split on the
   union and swap sides

This is your first time completing a full set equality for a
commutativity law. The pattern — `ext` followed by element-level
reasoning — is the standard technique for all set equalities.
"

/-- Union is commutative. -/
Statement (α : Type) (s t : Set α) : s ∪ t = t ∪ s := by
  Hint "Start with `ext x` to reduce to element-wise membership."
  ext x
  Hint "Use `constructor` to split the biconditional into two directions."
  constructor
  -- Forward: x ∈ s ∪ t → x ∈ t ∪ s
  · Hint "This is the same argument as Level 10. Case-split on the union
    and swap sides."
    Hint (hidden := true) "`intro hx` then `cases hx with | inl hs | inr ht`,
    and in each case use `right`/`left` with the hypothesis."
    intro hx
    cases hx with
    | inl hs =>
      Hint "`hs : x ∈ s`. The goal is `x ∈ t ∪ s` — use `right`."
      right
      exact hs
    | inr ht =>
      Hint "`ht : x ∈ t`. The goal is `x ∈ t ∪ s` — use `left`."
      left
      exact ht
  -- Backward: x ∈ t ∪ s → x ∈ s ∪ t
  · Hint "Same argument, swapped. Case-split and choose the opposite side."
    Hint (hidden := true) "`intro hx` then `cases hx with | inl ht | inr hs`,
    then `right`/`left`."
    intro hx
    cases hx with
    | inl ht =>
      right
      exact ht
    | inr hs =>
      left
      exact hs

Conclusion "
You proved the full set equality `s ∪ t = t ∪ s` by combining `ext`
with the element-level case analysis from Level 10.

This is the standard pattern for proving set equalities:
1. `ext x` — reduce to `x ∈ LHS ↔ x ∈ RHS`
2. `constructor` — split into two implications
3. Prove each direction using element-level tactics

Notice the proof has a symmetric structure: each direction swaps `left`
and `right`. This makes sense — commutativity is a symmetric property.

The intersection commutativity `s ∩ t = t ∩ s` (`Set.inter_comm`) works
the same way: `ext`, then `constructor`, then swap the `obtain`
components in each direction.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.union_comm sup_comm Or.comm
