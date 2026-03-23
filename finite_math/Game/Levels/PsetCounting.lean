import Game.Levels.PsetCounting.L01_EqualSizes
import Game.Levels.PsetCounting.L02_OvercrowdedMapping
import Game.Levels.PsetCounting.L03_ComposedBounds
import Game.Levels.PsetCounting.L04_LeagueDivisions
import Game.Levels.PsetCounting.L05_CategorySizes
import Game.Levels.PsetCounting.L06_IndirectBound
import Game.Levels.PsetCounting.L07_ChainedBounds
import Game.Levels.PsetCounting.L08_Boss

World "PsetCounting"
Title "Problem Set: Counting Techniques"

Introduction "
# Problem Set: Counting Techniques

You've completed the CountingTechniques world, learning four
major proof techniques for combinatorics:

1. **Bijective counting** -- equal cardinality from bijections
   (`card_congr`, `le_antisymm`)
2. **Injection/surjection bounds** -- cardinality inequalities
   (`card_le_of_injective`, `card_le_of_surjective`)
3. **The Pigeonhole Principle** -- too many pigeons forces
   a collision (`not_injective_of_card_lt`,
   `exists_ne_map_eq_of_card_lt`)
4. **Double counting** -- count the same set two ways
   (`card_eq_sum_card_fiberwise`, `sum_le_sum`)

Here, you must recognize which technique applies and execute
the proof independently. The levels progress from
single-technique retrieval to multi-technique integration.
"
