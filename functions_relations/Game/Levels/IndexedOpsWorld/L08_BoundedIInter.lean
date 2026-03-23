import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 8

Title "Bounded Indexed Intersection"

Introduction "
# Bounded Indexed Intersections

In Level 7, you learned `Set.mem_iUnion₂` for bounded indexed unions
(`⋃ i ∈ t, s i`). Now learn its dual for bounded indexed intersections:

$$x \\in \\bigcap_{i \\in t} s_i \\;\\Longleftrightarrow\\;
\\forall\\, i \\in t,\\; x \\in s_i$$

**New tool**: `rw [Set.mem_iInter₂]` converts `x ∈ ⋂ i ∈ t, s i` into
`∀ i, i ∈ t → x ∈ s i`. This is the bounded analogue of
`rw [Set.mem_iInter]`, just as `mem_iUnion₂` was the bounded analogue
of `mem_iUnion`.

The key pattern: after rewriting, you get a **universal with a
membership guard** — to use it, you provide both the index AND the
proof that the index is in bounds.

Compare the bounded and unbounded intersection patterns:

| Variant | After `rw` | To specialize |
|---|---|---|
| `⋂ i, s i` | `∀ i, x ∈ s i` | `hx i` |
| `⋂ i ∈ t, s i` | `∀ i, i ∈ t → x ∈ s i` | `hx j hj` |

**Your task**: Prove that the bounded intersection `⋂ i ∈ t, s i` is
a subset of `s j` whenever `j ∈ t`. This is the bounded analogue of
Level 3 (`⋂ i, s i ⊆ s j`).
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂
NewDefinition Set.iUnion Set.iInter
TheoremTab "Set"

/-- The bounded intersection is a subset of each in-bounds member. -/
Statement (α : Type) (ι : Type) (t : Set ι) (s : ι → Set α)
    (j : ι) (hj : j ∈ t) : ⋂ i ∈ t, s i ⊆ s j := by
  Hint "The goal is a subset relation. Start with `intro x hx`."
  intro x hx
  Hint "You have `hx : x ∈ ⋂ i ∈ t, s i`. Use `rw [Set.mem_iInter₂] at hx`
  to convert to `∀ i, i ∈ t → x ∈ s i`."
  Hint (hidden := true) "`rw [Set.mem_iInter₂] at hx` then `exact hx j hj`."
  rw [Set.mem_iInter₂] at hx
  Hint "Now `hx : ∀ i, i ∈ t → x ∈ s i`. You need `x ∈ s j`, and you
  know `j ∈ t` from `hj`. Specialize: `exact hx j hj`."
  exact hx j hj

Conclusion "
You proved that `⋂ i ∈ t, s i ⊆ s j` — the bounded intersection is
contained in each in-bounds member. Compare the unbounded and bounded
extraction patterns:

| Variant | After `rw` at hypothesis | Specialize |
|---|---|---|
| `⋂ i, s i` | `hx : ∀ i, x ∈ s i` | `hx j` |
| `⋂ i ∈ t, s i` | `hx : ∀ i, i ∈ t → x ∈ s i` | `hx j hj` |

The bounded variant adds one extra argument: the proof that the index
is in the bounding set. This mirrors the double `use` from bounded
unions, but on the universal (forall) side instead of the existential.

**The duality is now complete**:

| Operation | Bounded variant | Logic |
|---|---|---|
| `⋃ i ∈ t, s i` | `∃ i ∈ t, x ∈ s i` | bounded `∃` |
| `⋂ i ∈ t, s i` | `∀ i ∈ t, x ∈ s i` | bounded `∀` |

In ordinary math: \"If $x \\in \\bigcap_{i \\in t} s_i$ and $j \\in t$,
then by definition $x \\in s_i$ for every $i \\in t$; in particular,
$x \\in s_j$.\"
"

/-- `Set.biInter_subset_of_mem` states that for `j ∈ t`,
`⋂ i ∈ t, s i ⊆ s j`. -/
TheoremDoc Set.biInter_subset_of_mem as "Set.biInter_subset_of_mem" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.biInter_subset_of_mem Set.iInter₂_subset biInf_le
