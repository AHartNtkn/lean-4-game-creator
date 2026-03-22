import Game.Levels.PsetCombinatorics.L01_BackwardPascal
import Game.Levels.PsetCombinatorics.L02_PowersetSymmetry
import Game.Levels.PsetCombinatorics.L03_WeightedRowSum
import Game.Levels.PsetCombinatorics.L04_BinomialTheoremRetrieval
import Game.Levels.PsetCombinatorics.L05_AbsorptionIdentity
import Game.Levels.PsetCombinatorics.L06_FactorialFormula
import Game.Levels.PsetCombinatorics.L07_HockeyStickRetrieval
import Game.Levels.PsetCombinatorics.L08_RecognitionChallenge
import Game.Levels.PsetCombinatorics.L09_ConcreteVerification
import Game.Levels.PsetCombinatorics.L10_TwoIdentityChain
import Game.Levels.PsetCombinatorics.L11_WeightedBinomialSum
import Game.Levels.PsetCombinatorics.L12_AntidiagonalDoubleSum
import Game.Levels.PsetCombinatorics.L13_SumCongrWarmup
import Game.Levels.PsetCombinatorics.L14_Boss

World "PsetCombinatorics"
Title "Problem Set: Combinatorics"

Introduction "
# Problem Set: Combinatorics

You've completed four worlds on combinatorics:

- **BinomialCoefficients**: `choose_zero_right`, `choose_self`,
  `choose_succ_succ` (Pascal's identity), `choose_symm`,
  `choose_eq_zero_of_lt`, `choose_one_right`,
  `choose_mul_factorial_mul_factorial`, `add_one_mul_choose_eq`,
  the hockey stick identity by induction

- **Powerset**: `mem_powerset`, `card_powerset` ($2^n$ subsets),
  `card_powersetCard` ($\\binom{n}{k}$ subsets of size $k$),
  `powerset_mono`, complement counting

- **BinomialTheorem**: `add_pow_nat`, the specialize-simplify-rewrite
  pattern, row sum ($\\sum \\binom{n}{m} = 2^n$), weighted row sum,
  alternating sum over $\\mathbb{Z}$

- **PascalsTriangle**: `antidiagonal`, `mem_antidiagonal`,
  `sum_antidiagonal_eq_sum_range_succ_mk` (reindexing),
  `sum_antidiagonal_swap` (coordinate symmetry),
  `add_choose_eq` (Vandermonde), the sum of squared binomials

In the lecture worlds, each level told you which identity to apply.
Here, **choosing the right identity is part of the problem**. The
core skill shifts from *how to use a tool* to *which tool to reach
for* — retrieval and recognition under reduced scaffolding.

The levels progress from retrieval to transfer to integration:

1. Backward Pascal telescoping
2. Powerset symmetry counting
3. Weighted alternating sum over $\\mathbb{Z}$
4. Binomial theorem retrieval ($x = 3, y = 2$)
5. Absorption identity through powerset
6. Factorial formula through powerset
7. Hockey stick retrieval ($k = 2$)
8. Recognition challenge: identify the identity
9. Concrete verification: check the numbers
10. Two-identity chain: symmetry meets absorption
11. Weighted binomial sum: absorption inside a sum
12. Antidiagonal double row sum
13. Pointwise rewriting with `sum_congr rfl`
14. Boss: Vandermonde through powerset
"
