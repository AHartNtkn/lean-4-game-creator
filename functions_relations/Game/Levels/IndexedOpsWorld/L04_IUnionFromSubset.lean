import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 4

Title "Subset of Indexed Union"

Introduction "
# Building the Other Direction

You just proved that `⋂ i, s i ⊆ s j` — the intersection is
contained in each member. Now prove the dual: each member `s j`
is contained in the indexed union `⋃ i, s i`.

This is the indexed version of `s ⊆ s ∪ t`. If an element is in
`s j` for some `j`, then it is certainly in the union of the whole
family.

**Proof strategy**: To prove `x ∈ ⋃ i, s i`, rewrite to `∃ i, x ∈ s i`
and provide the witness `j`.
"

NewTheorem Set.mem_iUnion Set.mem_iInter
NewDefinition Set.iUnion Set.iInter
TheoremTab "Set"

/-- Each member of the family is a subset of the indexed union. -/
Statement (α : Type) (ι : Type) (s : ι → Set α) (j : ι) :
    s j ⊆ ⋃ i, s i := by
  Hint "Start with `intro x hx` to assume `x ∈ s j`."
  intro x hx
  Hint "The goal is `x ∈ ⋃ i, s i`. Use `rw [Set.mem_iUnion]` to
  convert to `∃ i, x ∈ s i`."
  rw [Set.mem_iUnion]
  Hint "Now provide the witness. You know `x ∈ s j`, so the
  witness index is `j`. Use `use j`."
  Hint (hidden := true) "`use j` — Lean will automatically apply `hx`
  to close the remaining goal."
  use j

Conclusion "
You proved `s j ⊆ ⋃ i, s i` — each set in the family is contained
in the indexed union. Together with Level 3, you now know:

- `⋂ i, s i ⊆ s j` — the intersection is inside each member
- `s j ⊆ ⋃ i, s i` — each member is inside the union

These are the indexed analogues of:
- `s ∩ t ⊆ s` (intersection is inside each factor)
- `s ⊆ s ∪ t` (each factor is inside the union)

In ordinary math: \"If $x \\in s_j$, then there exists an index
(namely $j$) such that $x \\in s_j$. Therefore $x \\in \\bigcup_i s_i$.\"
"

/-- `Set.subset_iUnion` states `s j ⊆ ⋃ i, s i` — each member of
the family is contained in the indexed union. -/
TheoremDoc Set.subset_iUnion as "Set.subset_iUnion" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.subset_iUnion le_iSup
