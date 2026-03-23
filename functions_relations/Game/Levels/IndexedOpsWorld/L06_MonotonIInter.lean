import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 6

Title "Monotonicity of Indexed Intersection"

Introduction "
# Monotonicity of Indexed Intersection

In the previous level, you proved that indexed union is monotone:
if each `s i ⊆ t i`, then `⋃ i, s i ⊆ ⋃ i, t i`. Now prove the
**dual** for indexed intersection:

$$\\forall\\, i,\\; s_i \\subseteq t_i \\;\\Longrightarrow\\;
\\bigcap_i s_i \\subseteq \\bigcap_i t_i$$

The proof is simpler than the union case because there is no `∃`
to extract — both sides are `∀` statements. You unwrap the `⋂` on
both hypothesis and goal to get universals, then apply the pointwise
subset.

**Proof strategy**: Unwrap the intersection hypothesis to get
`∀ i, x ∈ s i`, unwrap the goal to get `∀ i, x ∈ t i`, introduce
the index, and transfer membership via `h i`.
"

NewTheorem Set.mem_iUnion Set.mem_iInter
NewDefinition Set.iUnion Set.iInter
TheoremTab "Set"

/-- Indexed intersection is monotone: if each s i ⊆ t i, then ⋂ i, s i ⊆ ⋂ i, t i. -/
Statement (α : Type) (ι : Type) (s t : ι → Set α)
    (h : ∀ i, s i ⊆ t i) : ⋂ i, s i ⊆ ⋂ i, t i := by
  Hint "The goal is a subset relation. Start with `intro x hx`."
  intro x hx
  Hint "You have `hx : x ∈ ⋂ i, s i`. Use `rw [Set.mem_iInter] at hx`
  to convert to `∀ i, x ∈ s i`."
  rw [Set.mem_iInter] at hx
  Hint "Now rewrite the goal: `rw [Set.mem_iInter]` to convert to
  `∀ i, x ∈ t i`."
  rw [Set.mem_iInter]
  Hint "The goal is `∀ i, x ∈ t i`. Introduce the index with `intro i`."
  intro i
  Hint "You need `x ∈ t i`. You have `hx : ∀ i, x ∈ s i` (so `hx i`
  gives `x ∈ s i`) and `h : ∀ i, s i ⊆ t i` (so `h i` gives
  `s i ⊆ t i`). Apply the subset: `exact h i (hx i)`."
  Hint (hidden := true) "`exact h i (hx i)` — apply the pointwise
  subset at index `i` to the membership `hx i`."
  exact h i (hx i)

Conclusion "
You proved monotonicity of indexed intersection. The proof is simpler
than the union case because both sides reduce to `∀`:

```
intro x hx
rw [Set.mem_iInter] at hx    -- hx : ∀ i, x ∈ s i
rw [Set.mem_iInter]            -- goal: ∀ i, x ∈ t i
intro i                        -- goal: x ∈ t i
exact h i (hx i)               -- transfer via subset
```

**Compare union and intersection monotonicity**:

| Operation | Pattern | Key difference |
|---|---|---|
| `⋃` (Level 5) | extract `∃`, reuse witness, repack `∃` | must handle existentials |
| `⋂` (this level) | unwrap `∀`, introduce index, apply subset | only universals |

The intersection version is simpler because `∀` requires no
witness management — you just introduce the index and work with it.
The union version required extracting and repacking a witness index.

In ordinary math: \"If $x \\in \\bigcap_i s_i$, then $x \\in s_i$ for
every $i$. Since $s_i \\subseteq t_i$, we have $x \\in t_i$ for every
$i$. Therefore $x \\in \\bigcap_i t_i$.\"
"

/-- `Set.iInter_mono` states that indexed intersection is monotone:
if `∀ i, s i ⊆ t i` then `⋂ i, s i ⊆ ⋂ i, t i`. -/
TheoremDoc Set.iInter_mono as "Set.iInter_mono" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.iInter_mono iInf_mono
