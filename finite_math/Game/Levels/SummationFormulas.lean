import Game.Levels.SummationFormulas.L01_ConstantSum
import Game.Levels.SummationFormulas.L02_GaussSum
import Game.Levels.SummationFormulas.L03_OddNumbers
import Game.Levels.SummationFormulas.L04_SumOfSquares
import Game.Levels.SummationFormulas.L05_GeometricSum
import Game.Levels.SummationFormulas.L06_GeometricSum3
import Game.Levels.SummationFormulas.L07_GeneralGeometricSum
import Game.Levels.SummationFormulas.L08_ExponentialBound
import Game.Levels.SummationFormulas.L09_ProductBasics
import Game.Levels.SummationFormulas.L10_FactorialCompute
import Game.Levels.SummationFormulas.L11_Factorial
import Game.Levels.SummationFormulas.L12_TelescopingSum
import Game.Levels.SummationFormulas.L13_SumComm
import Game.Levels.SummationFormulas.L14_Boss

World "SummationFormulas"
Title "Summation Formulas"

Introduction "
# Classical Summation Formulas

You've learned two ways to prove big-operator identities:

- **Algebraic** (BigOpAlgebra): apply structural lemmas like
  `sum_add_distrib`, `sum_const`, `sum_union` to transform sums
  without computing them.

- **Finset induction** (FinsetInduction): induct on an arbitrary
  finset using `Finset.induction_on`, with base case `∅` and
  step `insert a s`.

This world introduces a third approach: **natural number induction**
combined with `sum_range_succ`. When a sum runs over
`Finset.range n = {0, 1, ..., n-1}`, you induct on `n` directly:

- **Base case** ($n = 0$): `sum_range_zero` clears the empty sum
- **Inductive step** ($n \\to n+1$): `sum_range_succ` peels off
  $f(n)$, then you substitute the IH and close with `ring`

This **range-peel + IH + ring** pattern is mechanical — the
mathematical content lives in the formula itself, not in the
proof technique. You'll use it to prove the Gauss sum, the sum
of squares, the sum of odd numbers, the geometric series (specific
and general), and a factorial identity.

**World structure**:
- **Levels 1-7** (Sum side): Classical summation formulas using
  `sum_range_zero`/`succ`, progressing from `ring` closers to
  the `have + ring + omega` technique for exponential formulas.
- **Level 8** (Inequality induction): The same technique applied
  to an inequality — showing that `have + ring + omega` handles
  bounds, not just equalities.
- **Levels 9-11** (Product mini-arc): Product analogues of the
  range tools, the factorial, and the factorial-as-product
  connection.
- **Level 12** (Telescoping): A telescoping sum that
  reveals why $\\sum (2i+1) = n^2$ — each term is $(i+1)^2 - i^2$.
- **Level 13** (Double counting): Swapping the order of a double
  sum — the formal foundation of the double-counting technique.
- **Level 14** (Boss): Integrates the sum-side tools with the
  factorial to prove a telescoping sum identity.

**Prerequisites**: `sum_range_succ` and `ring` from BigOpAlgebra,
`induction` from FinsetInduction.
"
