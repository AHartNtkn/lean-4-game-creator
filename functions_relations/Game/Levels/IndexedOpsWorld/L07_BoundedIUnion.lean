import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 7

Title "Bounded Indexed Union"

Introduction "
# Bounded Indexed Unions

So far, the indexed union `⋃ i, s i` ranges over ALL values of the
index type `ι`. But often you want to restrict the index to a subset.
For example, if you have sets indexed by all natural numbers but only
care about the first ten, `⋃ i ∈ Finset.range 10, s i` restricts the
union to those ten indices. Bounded variants let you union or intersect
over a sub-collection without changing the index type.

More precisely:

$$\\bigcup_{i \\in t} s_i = \\{x \\mid \\exists\\, i \\in t,\\; x \\in s_i\\}$$

In Lean, this is written `⋃ i ∈ t, s i`.

**New tool**: `rw [Set.mem_iUnion₂]` converts membership in a bounded
indexed union into a **double existential**:

`x ∈ ⋃ i ∈ t, s i  ↔  ∃ i, ∃ (_ : i ∈ t), x ∈ s i`

The key difference from unbounded `⋃ i, s i` is that after providing
the witness index `i`, you must ALSO prove that `i ∈ t`. This gives
a two-step `use` pattern:

1. `use j` — provide the witness index
2. `use hj` — provide the proof that `j ∈ t`

**Your task**: Prove that `s j ⊆ ⋃ i ∈ t, s i` when `j ∈ t`. This
is the bounded analogue of Level 4 (`s j ⊆ ⋃ i, s i`), with the
extra obligation of proving the index is in bounds.
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂
NewDefinition Set.iUnion Set.iInter
TheoremTab "Set"

/-- Each member of a bounded family is a subset of the bounded union. -/
Statement (α : Type) (ι : Type) (t : Set ι) (s : ι → Set α)
    (j : ι) (hj : j ∈ t) : s j ⊆ ⋃ i ∈ t, s i := by
  Hint "Start with `intro x hx` to assume `x ∈ s j`."
  intro x hx
  Hint "The goal is `x ∈ ⋃ i ∈ t, s i`. Use `rw [Set.mem_iUnion₂]`
  to convert to a double existential: `∃ i, ∃ (_ : i ∈ t), x ∈ s i`."
  rw [Set.mem_iUnion₂]
  Hint "The goal is now `∃ i, ∃ (_ : i ∈ t), x ∈ s i`. You need to
  provide two things: the witness index and the proof it is in `t`.

  Use `use j` to provide the index, then `use hj` to prove `j ∈ t`."
  Hint (hidden := true) "`use j` then `use hj`. Lean will close the
  remaining goal `x ∈ s j` using `hx`."
  use j, hj

Conclusion "
You proved `s j ⊆ ⋃ i ∈ t, s i` — each member of a bounded family
is contained in the bounded union, as long as the index is in bounds.

Compare the unbounded and bounded patterns:

| Variant | After `rw` | Proof pattern |
|---|---|---|
| `⋃ i, s i` | `∃ i, x ∈ s i` | `use j` |
| `⋃ i ∈ t, s i` | `∃ i, ∃ (_ : i ∈ t), x ∈ s i` | `use j, hj` |

The bounded variant adds one extra obligation: proving the witness
index belongs to the bounding set. This double-existential pattern
will appear whenever you work with restricted index ranges.

In ordinary math: \"If $j \\in t$ and $x \\in s_j$, then
$x \\in \\bigcup_{i \\in t} s_i$ because $j$ is a valid index.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.subset_iUnion Set.subset_biUnion_of_mem le_biSup
