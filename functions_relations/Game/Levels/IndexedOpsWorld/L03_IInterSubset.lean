import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 3

Title "Indexed Intersection Implies Membership"

Introduction "
# Using `mem_iInter` in a Hypothesis

In the previous level, you used `rw [Set.mem_iInter]` on the **goal**
to convert `x ∈ ⋂ i, s i` into `∀ i, x ∈ s i`. But `mem_iInter` is
just as useful on a **hypothesis**.

If you know `hx : x ∈ ⋂ i, s i`, then `rw [Set.mem_iInter] at hx`
converts `hx` to `hx : ∀ i, x ∈ s i`. After that, you can
**specialize** it to any particular index by writing `hx j`.

This is the fundamental pattern for *using* an indexed intersection:
unwrap the `∀`, then apply it to the index you need.

**Your task**: Prove that the indexed intersection of a family `s`
is a subset of `s j` for any particular index `j`. This is the
indexed analogue of `s ∩ t ⊆ s` — if an element is in every set,
it is certainly in any one of them.
"

NewTheorem Set.mem_iUnion Set.mem_iInter
NewDefinition Set.iUnion Set.iInter
TheoremTab "Set"

/-- The indexed intersection is a subset of each member of the family. -/
Statement (α : Type) (ι : Type) (s : ι → Set α) (j : ι) :
    ⋂ i, s i ⊆ s j := by
  Hint "The goal is a subset relation `⋂ i, s i ⊆ s j`. Start with
  `intro x hx` to assume `x ∈ ⋂ i, s i` and aim to prove `x ∈ s j`."
  intro x hx
  Hint "You have `hx : x ∈ ⋂ i, s i`. Use `rw [Set.mem_iInter] at hx`
  to unwrap it to `hx : ∀ i, x ∈ s i`."
  Hint (hidden := true) "`rw [Set.mem_iInter] at hx` then `exact hx j`."
  rw [Set.mem_iInter] at hx
  Hint "Now `hx : ∀ (i : ι), x ∈ s i`. The goal is `x ∈ s j`. Since
  `hx` holds for all `i`, apply it to `j`: `exact hx j`."
  exact hx j

Conclusion "
You proved that `⋂ i, s i ⊆ s j` — the intersection of all sets is
contained in each individual set. The proof shape is:

```
intro x hx                   -- assume x ∈ ⋂ i, s i
rw [Set.mem_iInter] at hx    -- unwrap: hx : ∀ i, x ∈ s i
exact hx j                   -- specialize to the index j
```

**The reusable pattern**: When a hypothesis involves `⋂`, rewrite
with `mem_iInter` to get a `∀`, then specialize to the index you need.
This is analogous to extracting `h.1` or `h.2` from an `∧` hypothesis —
but instead of two components, you have one for each index.

In ordinary math: \"If $x \\in \\bigcap_i s_i$, then by definition
$x \\in s_i$ for every $i$. In particular, $x \\in s_j$.\"
"

/-- `Set.iInter_subset` states `⋂ i, s i ⊆ s j` — the indexed
intersection is contained in each member of the family. -/
TheoremDoc Set.iInter_subset as "Set.iInter_subset" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.iInter_subset iInf_le
