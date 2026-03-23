import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 13

Title "Nonemptiness Propagates to Unions"

Introduction "
# Nonemptiness Propagation

In the previous level, you proved that a specific set is nonempty by
exhibiting a concrete witness. Now prove something more general: if
ANY member of a family is nonempty, then the indexed union is nonempty.

This combines two tools you have practiced:
- `Set.Nonempty` — existential over elements (`∃ x, x ∈ s`)
- `Set.mem_iUnion` — existential over indices (`∃ i, x ∈ s i`)

The proof chains two existentials: extract a witness from the nonempty
member, then place it in the union using the index.

**Your task**: Given that `s j` is nonempty, prove `⋃ i, s i` is nonempty.
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂ Set.mem_prod
NewDefinition Set.iUnion Set.iInter Set.prod Set.Nonempty
TheoremTab "Set"

/-- If some member of the family is nonempty, so is the indexed union. -/
Statement (α : Type) (ι : Type) (s : ι → Set α) (j : ι)
    (h : Set.Nonempty (s j)) : Set.Nonempty (⋃ i, s i) := by
  Hint "`h : Set.Nonempty (s j)` means `∃ x, x ∈ s j`. Extract the
  witness with `obtain ⟨x, hx⟩ := h`."
  obtain ⟨x, hx⟩ := h
  Hint "You have `x : α` with `hx : x ∈ s j`. The goal is
  `Set.Nonempty (⋃ i, s i)`, which means `∃ x, x ∈ ⋃ i, s i`.

  Use `use x` to provide the element witness."
  use x
  Hint "The goal is `x ∈ ⋃ i, s i`. Use `rw [Set.mem_iUnion]` to
  convert to `∃ i, x ∈ s i`, then provide the index `j`."
  Hint (hidden := true) "`rw [Set.mem_iUnion]` then `use j`."
  rw [Set.mem_iUnion]
  use j

Conclusion "
You proved that nonemptiness propagates from a member to the union.
The proof chained two existentials:

```
obtain ⟨x, hx⟩ := h       -- extract witness from s j
use x                       -- provide element for ⋃
rw [Set.mem_iUnion]         -- convert ⋃ to ∃
use j                       -- provide index for s j
```

**The pattern**: When you need to show a large set is nonempty, find
a specific member that is nonempty, extract its witness, and transfer
it to the larger set. This is a common argument in mathematics:
\"the union is nonempty because at least one of its pieces is.\"

**Does the converse hold?** If `⋃ i, s i` is nonempty, must some
`s j` be nonempty? Think about what tools you would need — you will
prove this in the next level.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.Nonempty.iUnion
