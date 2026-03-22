import Game.Levels.BigOpAlgebra.L01_SumAddDistrib
import Game.Levels.BigOpAlgebra.L02_ProdMulDistrib
import Game.Levels.BigOpAlgebra.L03_SumConst
import Game.Levels.BigOpAlgebra.L04_ProdConst
import Game.Levels.BigOpAlgebra.L05_SumCongrRetrieval
import Game.Levels.BigOpAlgebra.L06_SumUnion
import Game.Levels.BigOpAlgebra.L07_SumFilter
import Game.Levels.BigOpAlgebra.L08_SumComm
import Game.Levels.BigOpAlgebra.L09_CountingWithFilters
import Game.Levels.BigOpAlgebra.L10_ReorderingForSimplification
import Game.Levels.BigOpAlgebra.L11_SumRangeSucc
import Game.Levels.BigOpAlgebra.L12_RangeCombo
import Game.Levels.BigOpAlgebra.L13_ConcreteComputation
import Game.Levels.BigOpAlgebra.L14_CalcBlocks
import Game.Levels.BigOpAlgebra.L15_RingTactic
import Game.Levels.BigOpAlgebra.L16_CardSumBridge
import Game.Levels.BigOpAlgebra.L17_CoachingCardUnion
import Game.Levels.BigOpAlgebra.L18_Boss

World "BigOpAlgebra"
Title "Big Operators: Algebra"

Introduction "
# Big Operators: Algebraic Manipulation

In the BigOpIntro world, you learned to unfold sums and products
over concrete finsets using `sum_insert`, `sum_singleton`, and
`sum_congr`. Those are the *computational* tools — they let you
evaluate specific sums.

This world teaches the *algebraic* tools — structural
transformations that manipulate sums without computing them:

- **Linearity**: `∑(f + g) = ∑f + ∑g`
- **Products distribute**: `∏(f · g) = ∏f · ∏g`
- **Constant sums**: `∑ c = card · c`
- **Constant products**: `∏ c = c ^ card`
- **Union splitting**: `∑(s ∪ t) = ∑s + ∑t` (disjoint)
- **Filtering**: summing with a predicate guard
- **Double sum interchange**: `∑_x ∑_y = ∑_y ∑_x`
- **Range peeling**: `∑ range (n+1) = ∑ range n + f n`

You'll also learn two new proof-organization tools:
- **calc blocks** — chain multi-step equalities into readable proofs
- **ring** — automatically close algebraic rearrangements

A key insight: **cardinality is summation of 1s**. The theorem
`card_eq_sum_ones` bridges counting and summation, and you'll
use it in both directions throughout this world.

We focus primarily on the additive tools. Each additive identity
has a multiplicative twin (e.g., `prod_union` parallels
`sum_union`), and you'll see these in the documentation — the
proofs are structurally identical. The multiplicative tools are
available in your toolbox for later use.

**Prerequisites**: Everything from BigOpIntro (`sum_empty`,
`sum_singleton`, `sum_insert`, `sum_congr`, `card_eq_sum_ones`).
"
