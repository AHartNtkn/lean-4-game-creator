import Game.Levels.IndexedOpsWorld.L01_IndexedUnion
import Game.Levels.IndexedOpsWorld.L02_IndexedIntersection
import Game.Levels.IndexedOpsWorld.L03_IInterSubset
import Game.Levels.IndexedOpsWorld.L04_IUnionFromSubset
import Game.Levels.IndexedOpsWorld.L05_MonotonIUnion
import Game.Levels.IndexedOpsWorld.L06_MonotonIInter
import Game.Levels.IndexedOpsWorld.L07_BoundedIUnion
import Game.Levels.IndexedOpsWorld.L08_BoundedIInter
import Game.Levels.IndexedOpsWorld.L09_VacuousIntersection
import Game.Levels.IndexedOpsWorld.L10_VacuousUnion
import Game.Levels.IndexedOpsWorld.L11_CartesianProduct
import Game.Levels.IndexedOpsWorld.L12_Nonempty
import Game.Levels.IndexedOpsWorld.L13_NonemptyPropagation
import Game.Levels.IndexedOpsWorld.L14_NonemptyConverse
import Game.Levels.IndexedOpsWorld.L15_Powerset
import Game.Levels.IndexedOpsWorld.L16_PowersetMonotonicity
import Game.Levels.IndexedOpsWorld.L17_IUnionEqualsUniv
import Game.Levels.IndexedOpsWorld.L18_DeMorganUnion
import Game.Levels.IndexedOpsWorld.L19_DeMorganInter
import Game.Levels.IndexedOpsWorld.L20_NonemptyProduct
import Game.Levels.IndexedOpsWorld.L21_BoundedIntegration
import Game.Levels.IndexedOpsWorld.L22_IInterDistrib
import Game.Levels.IndexedOpsWorld.L23_Boss

World "IndexedOpsWorld"
Title "Indexed Operations World"

Introduction "
# Indexed Operations World

In Set Operations World, you learned the binary operations — `∪`, `∩`,
`ᶜ`, `\\` — and discovered that each one is a logical connective in
disguise. Now you will learn the **indexed** and **compound**
generalizations:

| Construction | Notation | Meaning |
|---|---|---|
| Indexed union | `⋃ i, s i` | `∃ i, x ∈ s i` |
| Indexed intersection | `⋂ i, s i` | `∀ i, x ∈ s i` |
| Bounded indexed union | `⋃ i ∈ t, s i` | `∃ i ∈ t, x ∈ s i` |
| Bounded indexed intersection | `⋂ i ∈ t, s i` | `∀ i ∈ t, x ∈ s i` |
| Cartesian product | `s ×ˢ t` | `p.1 ∈ s ∧ p.2 ∈ t` |
| Nonemptiness | `Set.Nonempty s` | `∃ x, x ∈ s` |
| Powerset | `𝒫 s` | `t ⊆ s` |

The indexed union `⋃ i, s i` collects everything that belongs to at
least one set in the family — it generalizes `∨` to `∃`. The indexed
intersection `⋂ i, s i` collects everything that belongs to every set
in the family — it generalizes `∧` to `∀`.

The cartesian product, nonemptiness, and powerset round out the set
constructions you will need for the rest of the course.

**New tools in this world**:
- `rw [Set.mem_iUnion]` — convert `⋃` membership to `∃`
- `rw [Set.mem_iInter]` — convert `⋂` membership to `∀`
- `rw [Set.mem_iUnion₂]` — convert bounded `⋃ i ∈ t` to double `∃`
- `rw [Set.mem_iInter₂]` — convert bounded `⋂ i ∈ t` to double `∀`
- `rw [Set.mem_prod]` — convert `×ˢ` membership to `∧`
- `rw [Set.mem_powerset_iff]` — convert `𝒫` membership to `⊆`

**Prerequisites**: Set World, Subset World, and Set Operations World.
"
