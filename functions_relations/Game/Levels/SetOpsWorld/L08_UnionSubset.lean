import Game.Metadata

World "SetOpsWorld"
Level 8

Title "Union and Subsets"

Introduction "
# s ⊆ s ∪ t

Just as intersection is a subset of each component, each component
is a subset of the union:

$$s \\subseteq s \\cup t$$

because if `x ∈ s`, then `x ∈ s ∨ x ∈ t` (by choosing the left side).

**Your task**: Prove this formally. After `intro x hx`, the goal
is `x ∈ s ∪ t`. Since this is a disjunction, use `left` to select
the left side, then close with `exact hx`.
"

/-- Every set is a subset of its union with another set. -/
Statement (α : Type) (s t : Set α) : s ⊆ s ∪ t := by
  Hint "Start with `intro x hx` for the subset proof."
  intro x hx
  Hint "The goal is `x ∈ s ∪ t`, which is a disjunction. Since you
  have `hx : x ∈ s`, the left side is what you want. Use `left`."
  Hint (hidden := true) "`left` then `exact hx`."
  Branch
    show x ∈ s ∨ x ∈ t
    left
    exact hx
  left
  Hint "The goal is `x ∈ s`, and `hx` is exactly that. Use `exact hx`."
  exact hx

Conclusion "
The proof is three lines: `intro x hx`, `left`, `exact hx`. Each
operation-to-logic correspondence gives you immediate subset facts:

| Fact | Proof sketch |
|---|---|
| `s ∩ t ⊆ s` | extract left component (`.1`) |
| `s ⊆ s ∪ t` | inject left component (`left`) |

These are dual: intersection *removes* information (you extract one
component), while union *adds* information (you inject one component).

The library names are `Set.subset_union_left` and
`Set.subset_union_right` (for `t ⊆ s ∪ t`).
"

/-- `Set.subset_union_left` proves `s ⊆ s ∪ t` — every set is
a subset of its union with another set.

## Statement
```
Set.subset_union_left : s ⊆ s ∪ t
```

## Proof idea
If `x ∈ s`, then `x ∈ s ∨ x ∈ t` by choosing left.
-/
TheoremDoc Set.subset_union_left as "Set.subset_union_left" in "Set"

/-- `Set.subset_union_right` proves `t ⊆ s ∪ t`. -/
TheoremDoc Set.subset_union_right as "Set.subset_union_right" in "Set"

/-- `le_sup_left` is the lattice version of `s ⊆ s ∪ t`. -/
TheoremDoc le_sup_left as "le_sup_left" in "Set"

/-- `le_sup_right` is the lattice version of `t ⊆ s ∪ t`. -/
TheoremDoc le_sup_right as "le_sup_right" in "Set"

NewTheorem Set.subset_union_left

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.subset_union_left Set.subset_union_right le_sup_left le_sup_right
