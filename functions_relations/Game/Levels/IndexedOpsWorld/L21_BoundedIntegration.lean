import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 21

Title "Bounded Intersection Inside Bounded Union"

Introduction "
# Integrating Bounded Variants

In Levels 7-8, you learned the bounded indexed operations `⋃ i ∈ t`
and `⋂ i ∈ t`. Now use BOTH in one proof.

**Claim**: If the bounding set `u` is nonempty (has some element `j`),
then the bounded intersection is contained in the bounded union:
`⋂ i ∈ u, s i ⊆ ⋃ i ∈ u, s i`.

This is intuitively obvious: if an element is in ALL of the `s i` for
`i ∈ u`, then it is certainly in SOME of them. But the formal proof
exercises both bounded rewrite lemmas together:

- `rw [Set.mem_iInter₂] at hx` on the hypothesis
- `rw [Set.mem_iUnion₂]` on the goal

**Proof plan**: Extract the universal from the bounded intersection
hypothesis, pick any valid index `j ∈ u`, and use it as the witness
for the bounded union.
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂ Set.mem_prod Set.mem_powerset_iff
NewDefinition Set.iUnion Set.iInter Set.prod Set.Nonempty Set.powerset
TheoremTab "Set"

/-- If u is nonempty, the bounded intersection is inside the bounded union. -/
Statement (α : Type) (ι : Type) (u : Set ι) (s : ι → Set α)
    (j : ι) (hj : j ∈ u) : ⋂ i ∈ u, s i ⊆ ⋃ i ∈ u, s i := by
  Hint "Start with `intro x hx` to assume `x ∈ ⋂ i ∈ u, s i`."
  intro x hx
  Hint "You have `hx : x ∈ ⋂ i ∈ u, s i`. Use
  `rw [Set.mem_iInter₂] at hx` to convert to
  `hx : ∀ i, i ∈ u → x ∈ s i`."
  rw [Set.mem_iInter₂] at hx
  Hint "Now convert the goal: `rw [Set.mem_iUnion₂]` to get
  `∃ i, ∃ (_ : i ∈ u), x ∈ s i`."
  rw [Set.mem_iUnion₂]
  Hint "The goal is a double existential. You need an index in `u` — you
  have `j` with `hj : j ∈ u`. Provide the witness: `use j, hj`."
  Hint (hidden := true) "`use j, hj` then `exact hx j hj`."
  use j, hj
  Hint "The goal is `x ∈ s j`. You have `hx : ∀ i, i ∈ u → x ∈ s i`.
  Apply it to `j` and `hj`: `exact hx j hj`."
  exact hx j hj

Conclusion "
You proved that `⋂ i ∈ u, s i ⊆ ⋃ i ∈ u, s i` — the bounded
intersection is inside the bounded union (assuming the bounding set
is nonempty).

This used both bounded rewrite lemmas together:

```
intro x hx
rw [Set.mem_iInter₂] at hx  -- hx : ∀ i, i ∈ u → x ∈ s i
rw [Set.mem_iUnion₂]          -- goal: ∃ i, ∃ _ : i ∈ u, x ∈ s i
use j, hj                     -- provide index and membership proof
exact hx j hj                 -- close with the universal
```

**Why nonemptiness matters**: Without `j ∈ u`, this is FALSE. Recall
from Level 9 that intersecting over an empty index gives `Set.univ`,
while unioning over nothing gives `∅`. So `⋂ i ∈ ∅, s i = Set.univ`
but `⋃ i ∈ ∅, s i = ∅`, and `Set.univ ⊆ ∅` is false.

**Vocabulary preview**: The set of all values of a function `f` is
called its *range*, written `Set.range f`. You will connect this to
indexed unions in the problem set — `Set.range f = ⋃ i, {f i}`.

In ordinary math: \"If $j \\in u$ and $x \\in \\bigcap_{i \\in u} s_i$,
then $x \\in s_j$ (specializing the intersection), hence
$x \\in \\bigcup_{i \\in u} s_i$ (witnessing the union with $j$).\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
