import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 16

Title "Powerset Monotonicity"

Introduction "
# Powerset Is Monotone

In the previous level, you proved a concrete powerset membership. Now
prove that the powerset operation is **monotone**: if `s ⊆ t`, then
`𝒫 s ⊆ 𝒫 t`.

In words: every subset of `s` is also a subset of `t`, because
being a subset of a smaller set is a stronger condition.

**Proof strategy**: To show `𝒫 s ⊆ 𝒫 t`, take an element `u ∈ 𝒫 s`,
convert to `u ⊆ s` using `mem_powerset_iff`, then use the hypothesis
`s ⊆ t` to conclude `u ⊆ t`, and convert back.

This level exercises `mem_powerset_iff` on BOTH a hypothesis and the
goal — a pattern you have not yet seen with the powerset.
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂ Set.mem_prod Set.mem_powerset_iff
NewDefinition Set.iUnion Set.iInter Set.prod Set.Nonempty Set.powerset
TheoremTab "Set"

/-- The powerset is monotone: if s ⊆ t, then 𝒫 s ⊆ 𝒫 t. -/
Statement (α : Type) (s t : Set α) (h : s ⊆ t) : 𝒫 s ⊆ 𝒫 t := by
  Hint "The goal is a subset relation between powersets. Start with
  `intro u hu` to assume `u ∈ 𝒫 s`."
  intro u hu
  Hint "You have `hu : u ∈ 𝒫 s`. Use `rw [Set.mem_powerset_iff] at hu`
  to convert to `u ⊆ s`."
  rw [Set.mem_powerset_iff] at hu
  Hint "Now convert the goal. Use `rw [Set.mem_powerset_iff]` to change
  the goal to `u ⊆ t`."
  rw [Set.mem_powerset_iff]
  Hint "The goal is `u ⊆ t`. You know `u ⊆ s` from `hu` and `s ⊆ t`
  from `h`. Chain them: `exact hu.trans h` — or equivalently,
  `exact Set.Subset.trans hu h`."
  Hint (hidden := true) "`exact hu.trans h` — subset transitivity chains
  `u ⊆ s` with `s ⊆ t` to get `u ⊆ t`."
  exact hu.trans h

Conclusion "
You proved that the powerset is monotone: `s ⊆ t → 𝒫 s ⊆ 𝒫 t`.

The proof used `mem_powerset_iff` in both directions:

```
intro u hu                       -- assume u ∈ 𝒫 s
rw [Set.mem_powerset_iff] at hu  -- hu : u ⊆ s
rw [Set.mem_powerset_iff]        -- goal: u ⊆ t
exact hu.trans h                  -- chain u ⊆ s ⊆ t
```

**The pattern**: When both hypothesis and goal involve `𝒫`, rewrite
both to subset relations and connect them with transitivity.

In ordinary math: \"If $u \\subseteq s$ and $s \\subseteq t$, then
$u \\subseteq t$. Therefore every member of $\\mathcal{P}(s)$ is a
member of $\\mathcal{P}(t)$.\"
"

/-- `Set.powerset_mono` states `s ⊆ t → 𝒫 s ⊆ 𝒫 t`. -/
TheoremDoc Set.powerset_mono as "Set.powerset_mono" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.powerset_mono
