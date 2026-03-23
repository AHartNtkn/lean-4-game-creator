import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 5

Title "Monotonicity of Indexed Union"

Introduction "
# Monotonicity of Indexed Union

If every set in one family is contained in the corresponding set of
another family, then the union of the first family is contained in the
union of the second. In symbols:

$$\\forall\\, i,\\; s_i \\subseteq t_i \\;\\Longrightarrow\\;
\\bigcup_i s_i \\subseteq \\bigcup_i t_i$$

This is the indexed analogue of the binary fact that
`s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ∪ t₁ ⊆ s₂ ∪ t₂`.

**Concrete example**: If `s k = {n | k ≤ n}` and `t k = {n | k ≤ n + 1}`,
then each `s k ⊆ t k` (every number at least `k` is also at least `k`
minus 1), so `⋃ k, s k ⊆ ⋃ k, t k`.

**Proof strategy**: To show `x ∈ ⋃ i, t i`, unpack `x ∈ ⋃ i, s i` to
find the witness index `i`, then use `h i` to transfer membership from
`s i` to `t i`, and re-pack into the union.

This level chains an indexed-union extraction (`mem_iUnion` on a
hypothesis) with a subset application and an indexed-union introduction
(`mem_iUnion` on the goal).
"

NewTheorem Set.mem_iUnion Set.mem_iInter
NewDefinition Set.iUnion Set.iInter
TheoremTab "Set"

/-- Indexed union is monotone: if each s i ⊆ t i, then ⋃ i, s i ⊆ ⋃ i, t i. -/
Statement (α : Type) (ι : Type) (s t : ι → Set α)
    (h : ∀ i, s i ⊆ t i) : ⋃ i, s i ⊆ ⋃ i, t i := by
  Hint "The goal is a subset relation. Start with `intro x hx`."
  intro x hx
  Hint "You have `hx : x ∈ ⋃ i, s i`. Use `rw [Set.mem_iUnion] at hx`
  to convert to `∃ i, x ∈ s i`, then extract the witness."
  rw [Set.mem_iUnion] at hx
  Hint "Now `hx : ∃ i, x ∈ s i`. Extract the witness with
  `obtain ⟨i, hsi⟩ := hx`."
  Hint (hidden := true) "`obtain ⟨i, hsi⟩ := hx` then `rw [Set.mem_iUnion]`
  then `use i` then `exact h i hsi`."
  obtain ⟨i, hsi⟩ := hx
  Hint "You have `hsi : x ∈ s i` and `h : ∀ i, s i ⊆ t i`. The goal is
  `x ∈ ⋃ i, t i`. Rewrite to an existential and reuse the same index."
  rw [Set.mem_iUnion]
  Hint "Use `use i` to provide the witness index."
  use i
  Hint "The goal is `x ∈ t i`. You know `s i ⊆ t i` from `h i`, and
  `hsi : x ∈ s i`. Apply the subset: `exact h i hsi`."
  exact h i hsi

Conclusion "
You proved monotonicity of indexed union. The proof pattern is:

```
intro x hx
rw [Set.mem_iUnion] at hx    -- unpack ⋃ from hypothesis
obtain ⟨i, hsi⟩ := hx        -- extract witness index
rw [Set.mem_iUnion]            -- prepare goal ⋃
use i                          -- reuse the same index
exact h i hsi                  -- transfer via subset
```

**The extract-transform-repack pattern**: This proof follows a
three-step strategy that recurs throughout indexed operations:

1. **Extract** — unpack the hypothesis to get a witness or universal
2. **Transform** — apply a given relationship (here, `h i`)
3. **Repack** — rebuild the goal using the transformed data

We will call this the *extract-transform-repack* pattern. You will
see it again in monotonicity of intersection (next level), De Morgan
laws, and the boss level.

In ordinary math: \"If $x \\in \\bigcup_i s_i$, then $x \\in s_j$ for
some $j$. Since $s_j \\subseteq t_j$, we have $x \\in t_j$. Therefore
$x \\in \\bigcup_i t_i$.\"
"

/-- `Set.iUnion_mono` states that indexed union is monotone:
if `∀ i, s i ⊆ t i` then `⋃ i, s i ⊆ ⋃ i, t i`. -/
TheoremDoc Set.iUnion_mono as "Set.iUnion_mono" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.iUnion_mono iSup_mono
