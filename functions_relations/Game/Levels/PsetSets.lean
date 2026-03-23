import Game.Levels.PsetSets.L01_UnivComplement
import Game.Levels.PsetSets.L02_ConcreteType
import Game.Levels.PsetSets.L03_DistributivitySubset
import Game.Levels.PsetSets.L04_PartitionEquality
import Game.Levels.PsetSets.L05_ComplementDifference
import Game.Levels.PsetSets.L06_ConverseComplementDiff
import Game.Levels.PsetSets.L07_NestedDifference
import Game.Levels.PsetSets.L08_NonemptyProduct
import Game.Levels.PsetSets.L09_IndexedSubset
import Game.Levels.PsetSets.L10_RangeForeshadow
import Game.Levels.PsetSets.L11_PowersetIntersection
import Game.Levels.PsetSets.L12_CounterexamplePowerset
import Game.Levels.PsetSets.L13_PowersetUnionSubset
import Game.Levels.PsetSets.L14_ComplementOfDifference
import Game.Levels.PsetSets.L15_SubsetViaDifference
import Game.Levels.PsetSets.L16_AbsorptionLaw
import Game.Levels.PsetSets.L17_IndexedDifference
import Game.Levels.PsetSets.L18_Boss

World "PsetSets"
Title "Problem Set: Sets"

Introduction "
# Problem Set: Sets

You have completed four worlds of set theory:
- **Set World**: Sets as predicates, membership, `show`/`change`
- **Subset World**: Subset relations, `ext`, `Set.Subset.antisymm`
- **Set Operations World**: Union, intersection, complement, difference,
  `push_neg`, `by_contra`, De Morgan
- **Indexed Operations World**: `⋃`/`⋂`, `×ˢ`, `Set.Nonempty`, `𝒫`,
  `Set.mem_iUnion`/`Set.mem_iInter`, `by_cases`

This problem set tests all these skills on **fresh problems** with
**less guidance**. The hints give strategy, not step-by-step instructions.

**What to expect**:
- Universal set and complement (Level 1)
- A concrete-type exercise on `Z` (Level 2)
- Distributivity on new arrangements (Level 3)
- A partition identity using `Set.Subset.antisymm` and `by_cases` (Level 4)
- Double negation and its converse (Levels 5–6)
- Nested differences (Level 7)
- Cartesian products and nonemptiness (Level 8)
- Indexed and powerset operations (Levels 9, 11)
- Retrieval of `Set.range` from Indexed Operations World (Level 10)
- A counterexample disproving a false generalization (Level 12)
- The powerset-union direction that DOES hold (Level 13)
- Complement of difference via by_contra + push_neg (Level 14)
- Subset characterized via set difference (Level 15)
- The absorption law (Level 16)
- Set difference over indexed union (Level 17)
- A boss integrating push_neg, indexed ops, and complement (Level 18)

You know everything you need. Trust your skills.
"
