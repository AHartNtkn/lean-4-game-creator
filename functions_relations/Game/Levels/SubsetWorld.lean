import Game.Levels.SubsetWorld.L01_FirstSubset
import Game.Levels.SubsetWorld.L02_ChangeTactic
import Game.Levels.SubsetWorld.L03_SubsetRefl
import Game.Levels.SubsetWorld.L04_EmptySubset
import Game.Levels.SubsetWorld.L05_SubsetUniv
import Game.Levels.SubsetWorld.L06_SubsetHypAsFunction
import Game.Levels.SubsetWorld.L07_NonSubset
import Game.Levels.SubsetWorld.L08_SubsetTrans
import Game.Levels.SubsetWorld.L09_NonArithSubset
import Game.Levels.SubsetWorld.L10_ExtIntro
import Game.Levels.SubsetWorld.L11_ExtPractice
import Game.Levels.SubsetWorld.L12_SetNonEquality
import Game.Levels.SubsetWorld.L13_Antisymm
import Game.Levels.SubsetWorld.L14_ProperSubset
import Game.Levels.SubsetWorld.L15_AntisymmFromExt
import Game.Levels.SubsetWorld.L16_ExtFromAntisymm
import Game.Levels.SubsetWorld.L17_Boss

World "SubsetWorld"
Title "Subset World"

Introduction "
# Subset World

In Set World, you learned that sets are predicates and membership is
predicate evaluation. Now you will learn the two fundamental
relationships between sets: **subset** (`⊆`) and **equality** (`=`).

A **subset** proof `s ⊆ t` means: for every element, if it is in `s`
then it is in `t`. The proof shape is always `intro x hx` — fix an
element, assume it is in the smaller set, then show it is in the
larger set.

A **set equality** proof `s = t` means: the two sets have exactly the
same elements. There are two routes:
- **Extensionality** (`ext`): prove `∀ x, x ∈ s ↔ x ∈ t` directly
- **Double containment** (`Set.Subset.antisymm`): prove `s ⊆ t` and
  `t ⊆ s` separately

By the end of this world, you will:
- Prove subset relations with the `intro x hx` pattern
- Handle the boundary cases `∅ ⊆ s` and `s ⊆ Set.univ`
- Use subset hypotheses as functions
- Disprove false subset claims by contradiction
- Chain subset proofs transitively
- Prove set equality via `ext` (extensionality)
- Prove set equality via `Set.Subset.antisymm` (double containment)
- Prove set non-equality by finding a contradictory witness
- Prove proper subset (`⊂`) by combining `⊆` and `¬⊆`
- Use `change` to unwrap set notation on hypotheses

You will also gain a new tactic (`ext`) and a new proof strategy
(double containment) that you will use throughout the rest of this
course.

**New tools in this world**:
- `change P at h` — unwrap a hypothesis to a definitionally equal form
- `ext x` — reduce set equality to element-wise membership
- `Set.Subset.antisymm` — derive equality from mutual subsets
"
