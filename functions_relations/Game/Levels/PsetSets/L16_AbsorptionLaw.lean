import Game.Metadata

World "PsetSets"
Level 16

Title "Absorption Law"

TheoremTab "Set"

Introduction "
# Problem Set: Level 16

Prove the **absorption law** for sets:

$$s \\cup (s \\cap t) = s$$

In words: taking the union of `s` with elements that are in BOTH `s`
and `t` gives back exactly `s` — because every element of `s ∩ t` is
already in `s`.

This is one of the fundamental Boolean algebra identities, alongside
De Morgan, distributivity, and the complement laws. It connects union
and intersection in a way that nothing else in Phase 1 does.
"

/-- The absorption law: s ∪ (s ∩ t) = s. -/
Statement (α : Type) (s t : Set α) : s ∪ (s ∩ t) = s := by
  Hint "Start with `ext x` then `constructor`."
  ext x
  constructor
  -- Forward: x ∈ s ∪ (s ∩ t) → x ∈ s
  · Hint "Case-split on the union. In both cases (`x ∈ s` or
    `x ∈ s ∩ t`), `x ∈ s` follows."
    Hint (hidden := true) "`intro hx` then `cases hx with | inl hs | inr hst`.
    Case `inl`: `exact hs`. Case `inr`: `exact hst.1`."
    intro hx
    cases hx with
    | inl hs =>
      Hint (hidden := true) "`hs : x ∈ s` — this is exactly the goal."
      exact hs
    | inr hst =>
      Hint (hidden := true) "`hst : x ∈ s ∩ t` — extract `.1` for `x ∈ s`."
      exact hst.1
  -- Backward: x ∈ s → x ∈ s ∪ (s ∩ t)
  · Hint "You need `x ∈ s ∪ (s ∩ t)`. Since `x ∈ s`, use `left`."
    Hint (hidden := true) "`intro hx` then `left` then `exact hx`."
    intro hx
    left
    exact hx

Conclusion "
You proved the absorption law `s ∪ (s ∩ t) = s`.

The proof was simple but illustrates an important point: the forward
direction required only that `s ∩ t ⊆ s` (which is always true), and
the backward direction required only that `s ⊆ s ∪ anything` (also
always true). Absorption holds because intersection makes things
*smaller* (so `s ∩ t` adds nothing to `s`).

**The dual absorption law** `s ∩ (s ∪ t) = s` also holds: intersecting
`s` with `s ∪ t` keeps exactly the elements of `s`, because every
element of `s` is automatically in `s ∪ t`. The proof uses the same
structure with swapped roles of `∩` and `∪`.

**Boolean algebra scorecard** — Phase 1 has now covered:
- Commutativity: `s ∪ t = t ∪ s`, `s ∩ t = t ∩ s`
- Distributivity: `s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u)`
- De Morgan: `(s ∪ t)ᶜ = sᶜ ∩ tᶜ`, `(s ∩ t)ᶜ = sᶜ ∪ tᶜ`
- Complement laws: `s ∩ sᶜ = ∅`, `s ∪ sᶜ = Set.univ`
- Double complement: `sᶜᶜ = s`
- Absorption: `s ∪ (s ∩ t) = s`
"

/-- `Set.union_inter_cancel_left` states `s ∪ s ∩ t = s`. -/
TheoremDoc Set.union_inter_cancel_left as "Set.union_inter_cancel_left" in "Set"

/-- `sup_inf_self` is the lattice version: `a ⊔ a ⊓ b = a`. -/
TheoremDoc sup_inf_self as "sup_inf_self" in "Set"

/-- `Set.inter_union_cancel_left` states `s ∩ (s ∪ t) = s` (dual absorption). -/
TheoremDoc Set.inter_union_cancel_left as "Set.inter_union_cancel_left" in "Set"

/-- `inf_sup_self` is the lattice version: `a ⊓ (a ⊔ b) = a`. -/
TheoremDoc inf_sup_self as "inf_sup_self" in "Set"

/-- `le_antisymm` states `a ≤ b → b ≤ a → a = b` (lattice antisymmetry). -/
TheoremDoc le_antisymm as "le_antisymm" in "Set"
/-- `sup_le` states `a ≤ c → b ≤ c → a ⊔ b ≤ c`. -/
TheoremDoc sup_le as "sup_le" in "Set"
/-- `inf_le_left` states `a ⊓ b ≤ a`. -/
TheoremDoc inf_le_left as "inf_le_left" in "Set"
/-- `le_sup_left` states `a ≤ a ⊔ b`. -/
TheoremDoc le_sup_left as "le_sup_left" in "Set"
/-- `le_sup_right` states `b ≤ a ⊔ b`. -/
TheoremDoc le_sup_right as "le_sup_right" in "Set"
/-- `inf_le_right` states `a ⊓ b ≤ b`. -/
TheoremDoc inf_le_right as "inf_le_right" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.union_inter_cancel_left sup_inf_self Set.inter_union_cancel_left inf_sup_self le_antisymm sup_le inf_le_left le_sup_left le_sup_right inf_le_right
