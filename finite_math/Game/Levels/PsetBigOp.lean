import Game.Levels.PsetBigOp.L01_ConcreteSum
import Game.Levels.PsetBigOp.L02_UnionConstantSum
import Game.Levels.PsetBigOp.L03_SumInduction
import Game.Levels.PsetBigOp.L04_DoubleSumSwap
import Game.Levels.PsetBigOp.L05_FilteredSum
import Game.Levels.PsetBigOp.L06_ProductInduction
import Game.Levels.PsetBigOp.L07_CalcChain
import Game.Levels.PsetBigOp.L08_TelescopingRetrieval
import Game.Levels.PsetBigOp.L09_Boss

World "PsetBigOp"
Title "Problem Set: Big Operators"

Introduction "
# Problem Set: Big Operators

You've completed four worlds on big operators and induction:

- **BigOpIntro**: `sum_empty`, `sum_insert`, `sum_singleton`,
  `sum_congr`, `card_eq_sum_ones`
- **BigOpAlgebra**: `sum_add_distrib`, `sum_const`, `sum_union`,
  `sum_comm`, `sum_filter`, `calc`, `ring`
- **FinsetInduction**: `Finset.induction_on`, the collect-and-close
  pattern for sums and products
- **SummationFormulas**: range-peel + IH + ring, the
  `have` + `ring` + `omega` technique, factorial

Now apply these skills to **fresh problems** with sparser hints
and no new definitions. The levels progress from retrieval to
transfer to integration:

1. Concrete sum computation
2. Union sum with a constant offset (`sum_const`)
3. Sum identity by finset induction
4. Double-sum interchange (`sum_comm`)
5. Filtered sum conversion (`sum_filter`)
6. Product identity by finset induction
7. Calc chain: sum-product decomposition
8. Telescoping retrieval: consecutive products
9. Boss: finset induction with natural subtraction
"
